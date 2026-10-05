package com.boox.einkdraw

import android.graphics.Bitmap
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.DashPathEffect
import android.graphics.Matrix
import android.graphics.Paint
import android.graphics.Path
import android.graphics.PorterDuff
import android.graphics.PorterDuffXfermode
import android.graphics.RectF
import com.onyx.android.sdk.data.note.TouchPoint
import com.onyx.android.sdk.pen.NeoCharcoalPen
import com.onyx.android.sdk.pen.NeoCharcoalPenV2
import com.onyx.android.sdk.pen.NeoBrushPen
import com.onyx.android.sdk.pen.NeoFountainPenV2
import com.onyx.android.sdk.pen.NeoMarkerPen
import com.onyx.android.sdk.pen.NeoMarkerPenWrapper
import com.onyx.android.sdk.pen.NeoPen
import com.onyx.android.sdk.pen.NeoPenConfig
import com.onyx.android.sdk.pen.NeoPenUtils
import com.onyx.android.sdk.pen.NeoRenderPoint
import com.onyx.android.sdk.pen.NeoSquarePen
import com.onyx.android.sdk.pen.PenResult
import kotlin.math.PI
import kotlin.math.abs
import kotlin.math.atan2
import kotlin.math.ceil
import kotlin.math.max
import kotlin.math.pow
import kotlin.math.sin
import kotlin.math.sqrt

/**
 * Software-canvas renderer that faithfully replicates each Onyx hardware stroke style.
 *
 * Native styles run through libneo_pen with [penConfig], the config the firmware uses for the
 * hardware preview, so committed strokes match what was previewed.
 *
 * Strategy per style:
 *  PENCIL     – round-cap polyline
 *  FOUNTAIN   – native Fountain V2 pen, drawn by point size
 *  MARKER     – native marker pen on an off-screen layer composited at 50% alpha
 *  NEO_BRUSH  – native brush pen, drawn by point size
 *  CHARCOAL   – native charcoal texture stamps (fallback: ring + dot cloud texture)
 *  DASH       – DashPathEffect line
 *  CHARCOAL_V2– native charcoal V2 texture stamps (fallback: ring + dot cloud texture)
 *  SQUARE_PEN – native square pen path results (fallback: trig approximation)
 */
object OnyxStrokeRenderer {

    private const val TAG = "OnyxStrokeRenderer"

    /**
     * libneo_pen config for [style], matching what the firmware uses for the hardware preview
     * (logged by the system process under the neo_lib tag, "createPen ... pen config").
     * Committed strokes must use the same config, or they render wider/thinner than the preview.
     * Null for styles not rendered by libneo_pen (pencil, dash).
     */
    fun penConfig(style: HardwarePenStyle, widthPx: Float): NeoPenConfig? {
        val config = NeoPenConfig().setWidth(widthPx)
        config.minWidth = 1f
        config.pressureSensitivity = 0.375f
        when (style) {
            HardwarePenStyle.FOUNTAIN -> {
                config.setWidth(widthPx + 3f)
                config.pressureSensitivity = 0.3f
                config.fastMode = true
            }
            HardwarePenStyle.MARKER, HardwarePenStyle.NEO_BRUSH -> Unit
            HardwarePenStyle.CHARCOAL, HardwarePenStyle.CHARCOAL_V2 -> {
                config.setTiltEnabled(true)
                config.pressureSensitivity = 1f
            }
            HardwarePenStyle.SQUARE_PEN -> {
                config.setWidth(widthPx * 2f)
                config.minWidth = 0.001f
                config.brushShape = NeoPenConfig.NEOPEN_BRUSH_SHAPE_RECTANGLE
                config.brushRatio = 10f
                // The firmware logs -45 but its y axis is flipped relative to the app canvas.
                config.brushAngle = 45f
            }
            HardwarePenStyle.PENCIL, HardwarePenStyle.DASH -> return null
        }
        return config
    }

    /**
     * Firmware stroke parameters (ViewUpdateHelper.setStrokeParameters) that make the hardware
     * preview follow [penConfig]. Only the charcoal layout is known: [tiltEnabled, tiltScale].
     */
    fun previewStrokeParameters(style: HardwarePenStyle): FloatArray? = when (style) {
        HardwarePenStyle.CHARCOAL, HardwarePenStyle.CHARCOAL_V2 -> penConfig(style, 1f)?.let {
            floatArrayOf(if (it.tiltEnabled) 1f else 0f, it.tiltScale)
        }
        else -> null
    }

    /** Native pen for [style], or null for pencil and dash. */
    private fun createPen(style: HardwarePenStyle, config: NeoPenConfig): NeoPen? = when (style) {
        HardwarePenStyle.FOUNTAIN -> NeoFountainPenV2.Companion.create(config)
        HardwarePenStyle.MARKER -> NeoMarkerPen.Companion.create(config)
        HardwarePenStyle.NEO_BRUSH -> NeoBrushPen.Companion.create(config)
        HardwarePenStyle.CHARCOAL -> NeoCharcoalPen.Companion.create(config)
        HardwarePenStyle.CHARCOAL_V2 -> NeoCharcoalPenV2.Companion.create(config)
        HardwarePenStyle.SQUARE_PEN -> NeoSquarePen.Companion.create(config)
        HardwarePenStyle.PENCIL, HardwarePenStyle.DASH -> null
    }

    /**
     * Run [points] through the native pen for a point-result style (fountain, marker, neo brush),
     * mirroring NeoPenUtils.computeStrokePoints but with [penConfig]. Null if the pen produced nothing.
     */
    private fun computeStrokePoints(
        style: HardwarePenStyle,
        points: List<TouchPoint>,
        widthPx: Float,
        pressureDivisor: Float,
    ): List<TouchPoint>? {
        if (points.size < 2) return null
        val config = penConfig(style, widthPx) ?: return null
        val pen = createPen(style, config) ?: return null
        val pts = points.toArrayList()
        val out = ArrayList<TouchPoint>(pts.size * 2)
        return try {
            for (p in pts) p.pressure /= pressureDivisor
            runPen(pen, pts).forEach { NeoPenUtils.readPointResult(it, out) }
            out.ifEmpty { null }
        } finally {
            runCatching { pen.destroy() }
        }
    }

    fun erase(
        style: HardwarePenStyle,
        points: List<TouchPoint>,
        widthPx: Float,
        canvas: Canvas,
        maxPressure: Float,
    ) {
        if (points.isEmpty()) return
        val w = canvas.width
        val h = canvas.height
        if (w <= 0 || h <= 0) return
        val mask = Bitmap.createBitmap(w, h, Bitmap.Config.ARGB_8888)
        try {
            val maskCanvas = Canvas(mask)
            render(style, points, widthPx, Color.BLACK, maskCanvas, maxPressure)
            normalizeMaskAlpha(mask)
            val clearPaint = Paint().apply {
                isFilterBitmap = false
                xfermode = PorterDuffXfermode(PorterDuff.Mode.DST_OUT)
            }
            canvas.drawBitmap(mask, 0f, 0f, clearPaint)
            clearPaint.xfermode = null
        } finally {
            mask.recycle()
        }
    }

    private fun normalizeMaskAlpha(mask: Bitmap) {
        val w = mask.width
        val h = mask.height
        if (w <= 0 || h <= 0) return
        val pixels = IntArray(w * h)
        mask.getPixels(pixels, 0, w, 0, 0, w, h)
        for (i in pixels.indices) {
            pixels[i] = if ((pixels[i] ushr 24) != 0) 0xFF000000.toInt() else 0
        }
        mask.setPixels(pixels, 0, w, 0, 0, w, h)
    }

    fun render(
        style: HardwarePenStyle,
        points: List<TouchPoint>,
        widthPx: Float,
        color: Int,
        canvas: Canvas,
        maxPressure: Float,
    ) {
        if (points.isEmpty()) return
        when (style) {
            HardwarePenStyle.PENCIL -> renderPencil(points, widthPx, color, canvas)
            HardwarePenStyle.FOUNTAIN -> renderFountain(points, widthPx, color, canvas, maxPressure)
            HardwarePenStyle.MARKER -> renderMarker(points, widthPx, color, canvas, maxPressure)
            HardwarePenStyle.NEO_BRUSH -> renderNeoBrush(points, widthPx, color, canvas, maxPressure)
            HardwarePenStyle.CHARCOAL, HardwarePenStyle.CHARCOAL_V2 -> renderCharcoal(style, points, widthPx, color, canvas, maxPressure)
            HardwarePenStyle.DASH -> renderDash(points, widthPx, color, canvas)
            HardwarePenStyle.SQUARE_PEN -> renderSquarePen(points, widthPx, color, canvas, maxPressure)
        }
    }

    // ─── PENCIL: round-cap polyline ──────────────────────────────────────────

    private fun renderPencil(points: List<TouchPoint>, widthPx: Float, color: Int, canvas: Canvas) {
        val paint = Paint().apply {
            this.color = color
            strokeWidth = widthPx
            style = Paint.Style.STROKE
            strokeCap = Paint.Cap.ROUND
            strokeJoin = Paint.Join.ROUND
            isAntiAlias = true
        }
        drawPolyline(points, canvas, paint)
    }

    // ─── FOUNTAIN: native Fountain V2 pen ─────────────────────────────────────

    private fun renderFountain(points: List<TouchPoint>, widthPx: Float, color: Int, canvas: Canvas, maxPressure: Float) {
        val paint = solidPaint(color)
        val pts = points.toArrayList()
        try {
            val pressureDivisor = nativePressureDivisor(pts, maxPressure)
            val result = computeStrokePoints(HardwarePenStyle.FOUNTAIN, pts, widthPx, pressureDivisor) ?: return
            com.onyx.android.sdk.pen.PenUtils.drawStrokeByPointSize(canvas, paint, result, false)
        } catch (_: Throwable) {
            fallbackPressureStroke(points, widthPx, color, canvas, HardwarePenStyle.FOUNTAIN, maxPressure)
        }
    }

    // ─── MARKER: native marker pen, 50 % alpha offscreen composite ──────────────

    private fun renderMarker(points: List<TouchPoint>, widthPx: Float, color: Int, canvas: Canvas, maxPressure: Float) {
        if (points.isEmpty()) return
        val pts = points.toArrayList()
        val paint = solidPaint(color).apply {
            strokeWidth = widthPx; isAntiAlias = true
            style = Paint.Style.FILL_AND_STROKE
            strokeCap = Paint.Cap.ROUND; strokeJoin = Paint.Join.ROUND
        }
        try {
            val result = computeStrokePoints(HardwarePenStyle.MARKER, pts, widthPx, nativePressureDivisor(pts, maxPressure)) ?: return
            NeoMarkerPenWrapper.drawStroke(canvas, paint, result, widthPx, false)
        } catch (e: Throwable) {
            android.util.Log.w(TAG, "marker native render failed, using software fallback", e)
            renderMarkerFallback(pts, widthPx, paint, canvas)
        }
    }

    /** Pure-Kotlin replica of NeoMarkerPenWrapper.drawStroke — no native library needed. */
    private fun renderMarkerFallback(pts: ArrayList<TouchPoint>, widthPx: Float, paint: Paint, canvas: Canvas) {
        // Set TouchPoint.size based on pressure (what the native engine computes)
        val stats = signalStats(pts)
        for (p in pts) {
            p.size = widthPx * (0.4f + 0.6f * normalizedSignal(p, stats))
        }
        // Draw into offscreen bitmap at 100% opacity
        val bmp = android.graphics.Bitmap.createBitmap(canvas.width, canvas.height, android.graphics.Bitmap.Config.ARGB_8888)
        val bmpCanvas = Canvas(bmp)
        com.onyx.android.sdk.pen.PenUtils.drawStrokeByPointSize(bmpCanvas, paint, pts, false)
        // Compute bounding rect and inset by half stroke-width (same as NeoMarkerPenWrapper)
        var rect: android.graphics.Rect? = null
        for (p in pts) {
            if (rect == null) rect = android.graphics.Rect(p.x.toInt(), p.y.toInt(), p.x.toInt(), p.y.toInt())
            else rect.union(p.x.toInt(), p.y.toInt())
        }
        if (rect == null) { bmp.recycle(); return }
        rect.inset(-(widthPx / 2f).toInt(), -(widthPx / 2f).toInt())
        // Composite at alpha=128 (50%) — exactly like NeoMarkerPenWrapper.drawStroke
        val savedAlpha = paint.alpha
        paint.alpha = 128
        canvas.drawBitmap(bmp, rect, rect, paint)
        paint.alpha = savedAlpha
        bmp.recycle()
    }

    // ─── NEO_BRUSH: native brush pen ─────────────────────────────────────────

    private fun renderNeoBrush(points: List<TouchPoint>, widthPx: Float, color: Int, canvas: Canvas, maxPressure: Float) {
        val pts = points.toArrayList()
        val paint = solidPaint(color)
        try {
            val pressureDivisor = nativePressureDivisor(pts, maxPressure)
            val result = computeStrokePoints(HardwarePenStyle.NEO_BRUSH, pts, widthPx, pressureDivisor)
            if (!result.isNullOrEmpty()) {
                com.onyx.android.sdk.pen.PenUtils.drawStrokeByPointSize(canvas, paint, result, false)
            } else {
                fallbackPressureStroke(points, widthPx, color, canvas, HardwarePenStyle.NEO_BRUSH, maxPressure)
            }
        } catch (_: Throwable) {
            fallbackPressureStroke(points, widthPx, color, canvas, HardwarePenStyle.NEO_BRUSH, maxPressure)
        }
    }

    // ─── CHARCOAL / CHARCOAL_V2 ──────────────────────────────────────────────

    private fun renderCharcoal(
        style: HardwarePenStyle,
        points: List<TouchPoint>,
        widthPx: Float,
        color: Int,
        canvas: Canvas,
        maxPressure: Float,
    ) {
        val v2 = style == HardwarePenStyle.CHARCOAL_V2
        if (points.size < 2) { charcoalCloudTexture(points, widthPx, color, canvas, v2); return }

        val prepared = prepareCharcoalPoints(points)
        val pressureDivisor = nativePressureDivisor(prepared, maxPressure)
        runCatching {
            if (!drawCharcoalWithHardwareLikeConfig(prepared, widthPx, color, canvas, pressureDivisor, style)) {
                val args = com.onyx.android.sdk.pen.PenRenderArgs()
                    .setCanvas(canvas)
                    .setPoints(prepared)
                    .setStrokeWidth(widthPx)
                    .setColor(color)
                    .setContentRect(RectF(0f, 0f, canvas.width.toFloat(), canvas.height.toFloat()))
                    .setPenType(if (v2) NeoPenConfig.NEOPEN_PEN_TYPE_CHARCOAL_V2 else NeoPenConfig.NEOPEN_PEN_TYPE_CHARCOAL)
                    .setScreenMatrix(Matrix())
                    .setRenderMatrix(Matrix())
                    .setTiltEnabled(penConfig(style, widthPx)?.tiltEnabled ?: true)
                    .setErase(false)
                    .setCreateArgs(com.onyx.android.sdk.data.note.ShapeCreateArgs().setMaxPressure(pressureDivisor))
                if (v2) {
                    com.onyx.android.sdk.pen.NeoCharcoalPenV2Wrapper.drawNormalStroke(args)
                } else {
                    com.onyx.android.sdk.pen.NeoCharcoalPenWrapper.drawNormalStroke(args)
                }
            }
        }.onFailure { e ->
            android.util.Log.w(TAG, "$style native render failed, using cloud texture", e)
            charcoalCloudTexture(points, widthPx, color, canvas, v2)
        }
    }

    /**
     * Replica of the charcoal wrapper call chain, using [penConfig] so the committed stroke
     * matches the hardware preview. False if the pen produced no stamps.
     */
    private fun drawCharcoalWithHardwareLikeConfig(
        points: List<TouchPoint>,
        widthPx: Float,
        color: Int,
        canvas: Canvas,
        pressureDivisor: Float,
        style: HardwarePenStyle,
    ): Boolean {
        if (points.size < 2) return false
        val safeMaxPressure = max(1f, pressureDivisor)
        val screenMatrix = Matrix()
        val penConfig = penConfig(style, widthPx)?.setColor(color)?.setMaxTouchPressure(safeMaxPressure) ?: return false
        val pen = createPen(style, penConfig) ?: return false

        val bitmaps = ArrayList<Bitmap>(512)
        return try {
            val mapped = NeoPenUtils.mapToPenCanvas(points, screenMatrix)
            if (mapped.size < 2) return false
            for (p in mapped) {
                p.pressure /= safeMaxPressure
            }

            val renderPoints = ArrayList<NeoRenderPoint>(mapped.size * 3)
            runPen(pen, mapped).forEach { NeoPenUtils.readTextureResult(it, bitmaps, renderPoints) }
            if (renderPoints.isEmpty() || bitmaps.isEmpty()) return false

            val inverse = Matrix()
            val mappedRenderPoints = if (screenMatrix.invert(inverse)) {
                NeoPenUtils.mapFromPenCanvas(renderPoints.toTypedArray(), bitmaps, inverse)
            } else {
                renderPoints.toTypedArray()
            }

            for (rp in mappedRenderPoints) {
                val idx = rp.bitmapIndex
                if (idx in 0 until bitmaps.size) {
                    canvas.drawBitmap(bitmaps[idx], rp.x, rp.y, null)
                }
            }
            true
        } finally {
            runCatching { pen.destroy() }
            bitmaps.forEach { bmp ->
                if (!bmp.isRecycled) runCatching { bmp.recycle() }
            }
        }
    }

    private fun runPen(pen: NeoPen, points: List<TouchPoint>): List<Pair<PenResult?, PenResult?>> {
        val results = ArrayList<Pair<PenResult?, PenResult?>>(3)
        invokePenDown(pen, points.first())?.let(results::add)
        if (points.size > 2) {
            invokePenMove(pen, points.subList(1, points.size - 1))?.let(results::add)
        }
        invokePenUp(pen, points.last())?.let(results::add)
        return results
    }

    @Suppress("UNCHECKED_CAST")
    private fun invokePenDown(
        pen: NeoPen,
        point: TouchPoint,
    ): Pair<PenResult?, PenResult?>? = runCatching {
        val basePoint = Class.forName("com.onyx.android.sdk.base.data.TouchPoint")
        val fn = pen.javaClass.getMethod("onPenDown", basePoint, Boolean::class.javaPrimitiveType)
        fn.invoke(pen, point, true) as? Pair<PenResult?, PenResult?>
    }.getOrNull()

    @Suppress("UNCHECKED_CAST")
    private fun invokePenMove(
        pen: NeoPen,
        points: List<TouchPoint>,
    ): Pair<PenResult?, PenResult?>? = runCatching {
        val basePoint = Class.forName("com.onyx.android.sdk.base.data.TouchPoint")
        val fn = pen.javaClass.getMethod("onPenMove", List::class.java, basePoint, Boolean::class.javaPrimitiveType)
        fn.invoke(pen, points, null, true) as? Pair<PenResult?, PenResult?>
    }.getOrNull()

    @Suppress("UNCHECKED_CAST")
    private fun invokePenUp(
        pen: NeoPen,
        point: TouchPoint,
    ): Pair<PenResult?, PenResult?>? = runCatching {
        val basePoint = Class.forName("com.onyx.android.sdk.base.data.TouchPoint")
        val fn = pen.javaClass.getMethod("onPenUp", basePoint, Boolean::class.javaPrimitiveType)
        fn.invoke(pen, point, true) as? Pair<PenResult?, PenResult?>
    }.getOrNull()

    private fun renderPenResultPairs(
        results: List<Pair<PenResult?, PenResult?>>,
        canvas: Canvas,
        paint: Paint,
    ) {
        for (pair in results) {
            pair.first?.draw(canvas, paint)
        }
        results.lastOrNull()?.second?.draw(canvas, paint)
    }

    private fun clearPenResultPairCache(results: List<Pair<PenResult?, PenResult?>>) {
        for (pair in results) {
            pair.first?.clearCache()
            pair.second?.clearCache()
        }
    }

    /** Copy of [points]; a stroke without pressure gets 0.35 everywhere so the native pen still draws. */
    private fun prepareCharcoalPoints(points: List<TouchPoint>): ArrayList<TouchPoint> {
        val out = points.toArrayList()
        if (out.none { it.pressure > 0f }) out.forEach { it.pressure = 0.35f }
        return out
    }

    /**
     * Native pen wrappers normalize by dividing point.pressure by this divisor.
     * RawInput can deliver either already-normalized [0..1] or raw [0..MAX] pressure.
     */
    private fun nativePressureDivisor(points: List<TouchPoint>, deviceMaxPressure: Float): Float {
        var maxP = 0f
        for (p in points) {
            if (p.pressure > 0f) maxP = max(maxP, p.pressure)
        }
        if (maxP <= 0f) return 1f
        return if (maxP <= 1.5f) 1f else max(deviceMaxPressure, maxP)
    }

    /** Pure-Java fallback: ring + dot cloud stamps along the stroke path. */
    private fun charcoalCloudTexture(points: List<TouchPoint>, widthPx: Float, color: Int, canvas: Canvas, v2: Boolean) {
        val paint = Paint().apply {
            this.color = withAlpha(color, 160) // Proper charcoal opacity layer
            strokeWidth = 1f
            style = Paint.Style.STROKE
            isAntiAlias = false
        }
        val stats = signalStats(points)
        if (points.size == 1) {
            val p = points[0]
            charcoalStamp(p.x, p.y, widthPx, normalizedSignal(p, stats), 0, canvas, paint, v2)
            return
        }
        var prev = points[0]
        for (i in 1 until points.size) {
            val curr = points[i]
            val ps = normalizedSignal(prev, stats); val cs = normalizedSignal(curr, stats)
            val dx = curr.x - prev.x; val dy = curr.y - prev.y
            val dist = sqrt(dx * dx + dy * dy)
            val step = if (v2) 8.5f else 9f
            val n = max(1, ceil(dist / step).toInt())
            for (s in 0..n) {
                val t = s.toFloat() / n
                charcoalStamp(prev.x + dx * t, prev.y + dy * t, widthPx, lerp(ps, cs, t), i * 8192 + s, canvas, paint, v2)
            }
            prev = curr
        }
    }

    private fun charcoalStamp(cx: Float, cy: Float, baseW: Float, sig: Float, seed: Int, canvas: Canvas, paint: Paint, v2: Boolean) {
        val outerR = max(0.8f, baseW * if (v2) 0.68f else 0.58f)
        val innerR = outerR * if (v2) 0.9f else 0.88f
        val edgeD = if (v2) lerp(0.0015f, 0.005f, sig) else lerp(0.002f, 0.006f, sig)
        val dotD = if (v2) lerp(0.001f, 0.0035f, sig) else lerp(0.0014f, 0.004f, sig)
        dotCloud(cx, cy, innerR, outerR, edgeD, seed, canvas, paint)
        dotCloud(cx, cy, 0f, outerR * 0.72f, dotD, seed + 97, canvas, paint)
        if (v2) dotCloud(cx, cy, outerR * 1.02f, outerR * 1.22f, lerp(0.001f, 0.003f, sig), seed + 211, canvas, paint)
    }

    private fun dotCloud(cx: Float, cy: Float, innerR: Float, outerR: Float, density: Float, seed: Int, canvas: Canvas, paint: Paint) {
        val n = max(1, (outerR * outerR * density * 0.1f).toInt())
        val innerRatioSq = if (outerR > 0) (innerR / outerR).pow(2) else 0f
        var drawn = 0; var attempt = 0
        while (drawn < n && attempt < n * 3) {
            val rx = hashUnit(seed, attempt * 2) * 2f - 1f
            val ry = hashUnit(seed, attempt * 2 + 1) * 2f - 1f
            val dSq = rx * rx + ry * ry
            if (dSq <= 1f && dSq >= innerRatioSq) { canvas.drawPoint(cx + rx * outerR, cy + ry * outerR, paint); drawn++ }
            attempt++
        }
    }

    // ─── DASH: black+white dashed track (matches Onyx overlay style) ─────────

    private fun renderDash(points: List<TouchPoint>, widthPx: Float, color: Int, canvas: Canvas) {
        if (points.isEmpty()) return

        val dashPeriod = max(2f, widthPx * 3f)
        val phase = 0f
        val offset = max(0.5f, widthPx / 3f)

        val basePaint = Paint().apply {
            style = Paint.Style.STROKE
            strokeCap = Paint.Cap.ROUND
            strokeJoin = Paint.Join.ROUND
            strokeWidth = widthPx
            isAntiAlias = true
        }
        val whiteDash = Paint(basePaint).apply {
            this.color = Color.WHITE
            pathEffect = DashPathEffect(
                floatArrayOf(max(1f, dashPeriod - offset), dashPeriod + offset),
                phase,
            )
        }
        val blackDash = Paint(basePaint).apply {
            this.color = color
            pathEffect = DashPathEffect(floatArrayOf(dashPeriod, dashPeriod), phase)
        }

        if (points.size == 1) {
            val p = points[0]
            val radius = max(0.75f, widthPx * 0.5f)
            val whiteDot = Paint(basePaint).apply {
                style = Paint.Style.FILL
                this.color = Color.WHITE
                pathEffect = null
            }
            val blackDot = Paint(basePaint).apply {
                style = Paint.Style.FILL
                this.color = color
                pathEffect = null
            }
            canvas.drawCircle(p.x + offset, p.y + offset, radius, whiteDot)
            canvas.drawCircle(p.x, p.y, radius, blackDot)
            return
        }

        val path = Path().apply {
            moveTo(points[0].x, points[0].y)
            for (i in 1 until points.size) lineTo(points[i].x, points[i].y)
        }
        canvas.save()
        canvas.translate(offset, offset)
        canvas.drawPath(path, whiteDash)
        canvas.restore()
        canvas.drawPath(path, blackDash)
    }

    // ─── SQUARE_PEN: NeoSquarePen (reference path from neo-reader) ──────────

    /**
     * NeoSquarePen with [penConfig]; falls back to a trig approximation if the native pen fails.
     */
    private fun renderSquarePen(
        points: List<TouchPoint>,
        widthPx: Float,
        color: Int,
        canvas: Canvas,
        maxPressure: Float,
    ) {
        if (points.isEmpty()) return
        val rendered = runCatching {
            renderSquarePenNative(points, widthPx, color, canvas, maxPressure)
        }.getOrDefault(false)
        if (!rendered) {
            renderSquarePenFallback(points, widthPx, color, canvas)
        }
    }

    private fun renderSquarePenNative(
        points: List<TouchPoint>,
        widthPx: Float,
        color: Int,
        canvas: Canvas,
        maxPressure: Float,
    ): Boolean {
        if (points.size < 2) {
            val paint = solidPaint(color).apply { style = Paint.Style.FILL }
            points.firstOrNull()?.let { canvas.drawCircle(it.x, it.y, widthPx / 2f, paint) }
            return true
        }

        val mapped = points.toArrayList()
        val pressureDivisor = nativePressureDivisor(mapped, maxPressure)
        for (p in mapped) p.pressure /= pressureDivisor

        val config = penConfig(HardwarePenStyle.SQUARE_PEN, widthPx)?.setColor(color) ?: return false
        val pen = createPen(HardwarePenStyle.SQUARE_PEN, config) ?: return false
        return try {
            val results = runPen(pen, mapped)
            if (results.isEmpty()) return false

            val paint = solidPaint(color).apply {
                style = Paint.Style.FILL
                strokeWidth = 0f
            }
            renderPenResultPairs(results, canvas, paint)
            clearPenResultPairCache(results)
            true
        } finally {
            runCatching { pen.destroy() }
        }
    }

    /**
     * Legacy approximation retained only if NeoSquarePen is unavailable.
     */
    private fun renderSquarePenFallback(points: List<TouchPoint>, widthPx: Float, color: Int, canvas: Canvas) {
        if (points.size < 2) {
            val paint = solidPaint(color).apply { style = Paint.Style.FILL }
            points.firstOrNull()?.let { canvas.drawCircle(it.x, it.y, widthPx / 2f, paint) }
            return
        }
        val nibAngle = (PI / 4.0).toFloat()
        val paint = Paint().apply {
            this.color = color
            style = Paint.Style.STROKE
            strokeCap = Paint.Cap.BUTT
            strokeJoin = Paint.Join.MITER
            isAntiAlias = true
        }
        var prev = points[0]
        for (i in 1 until points.size) {
            val curr = points[i]
            val dx = curr.x - prev.x
            val dy = curr.y - prev.y
            if (abs(dx) < 0.01f && abs(dy) < 0.01f) {
                prev = curr
                continue
            }
            val angle = atan2(dy, dx)
            val factor = max(0.12f, abs(sin(angle - nibAngle)))
            paint.strokeWidth = widthPx * factor
            canvas.drawLine(prev.x, prev.y, curr.x, curr.y, paint)
            prev = curr
        }
    }

    // ─── Shared utilities ─────────────────────────────────────────────────────

    private fun drawPolyline(points: List<TouchPoint>, canvas: Canvas, paint: Paint) {
        if (points.isEmpty()) return
        if (points.size == 1) {
            val p = points[0]; canvas.drawPoint(p.x, p.y, paint); return
        }
        val path = Path()
        path.moveTo(points[0].x, points[0].y)
        for (i in 1 until points.size) path.lineTo(points[i].x, points[i].y)
        canvas.drawPath(path, paint)
    }

    /**
     * Software fallback for the fountain and neo brush pens: filled circles along the stroke,
     * sized by pressure.
     */
    private fun fallbackPressureStroke(
        points: List<TouchPoint>,
        widthPx: Float,
        color: Int,
        canvas: Canvas,
        penStyle: HardwarePenStyle,
        maxPressure: Float,
    ) {
        val paint = solidPaint(color).apply { style = Paint.Style.FILL }
        val pressureDivisor = nativePressureDivisor(points, maxPressure)
        if (points.size == 1) {
            val p = points[0]
            canvas.drawCircle(p.x, p.y, max(0.5f, pressureToRadius(widthPx, normalizedSignalAbsolute(p, pressureDivisor), penStyle)), paint)
            return
        }
        var prev = points[0]
        for (i in 1 until points.size) {
            val curr = points[i]
            val pr = pressureToRadius(widthPx, normalizedSignalAbsolute(prev, pressureDivisor), penStyle)
            val cr = pressureToRadius(widthPx, normalizedSignalAbsolute(curr, pressureDivisor), penStyle)
            interpolateCircles(prev, curr, pr, cr, canvas, paint)
            prev = curr
        }
    }

    private fun interpolateCircles(start: TouchPoint, end: TouchPoint, sr: Float, er: Float, canvas: Canvas, paint: Paint) {
        val dx = end.x - start.x; val dy = end.y - start.y
        val dist = sqrt(dx * dx + dy * dy)
        if (dist <= 0.001f) { canvas.drawCircle(start.x, start.y, max(0.5f, sr), paint); return }
        val steps = max(1, ceil(dist / 0.8f).toInt())
        for (s in 0..steps) {
            val t = s.toFloat() / steps
            canvas.drawCircle(start.x + dx * t, start.y + dy * t, max(0.5f, lerp(sr, er, t)), paint)
        }
    }

    private fun solidPaint(color: Int) = Paint().apply {
        this.color = color
        isAntiAlias = true
        style = Paint.Style.FILL
        strokeCap = Paint.Cap.ROUND
        strokeJoin = Paint.Join.ROUND
    }

    private fun List<TouchPoint>.toArrayList(): ArrayList<TouchPoint> {
        val list = ArrayList<TouchPoint>(size)
        forEach { list.add(TouchPoint(it)) }
        return list
    }

    // ─── Signal / pressure helpers ────────────────────────────────────────────

    private data class SignalStats(val maxP: Float, val hasP: Boolean)

    private fun signalStats(points: List<TouchPoint>): SignalStats {
        var maxP = 0f; var hasP = false
        for (p in points) {
            if (p.pressure > 0f) { maxP = max(maxP, p.pressure); hasP = true }
        }
        return SignalStats(maxP, hasP)
    }

    private fun normalizedSignal(pt: TouchPoint, stats: SignalStats): Float {
        if (!stats.hasP || pt.pressure <= 0f) return 0.35f
        val norm = if (stats.maxP <= 1.05f) pt.pressure.coerceIn(0.01f, 1f)
                   else (pt.pressure / stats.maxP).coerceIn(0.01f, 1f)
        return norm.pow(0.85f).coerceIn(0.01f, 1f)
    }

    /**
     * Absolute pressure normalization (vs per-stroke relative), used by fallback
     * paths to avoid width spikes on short low-pressure strokes.
     */
    private fun normalizedSignalAbsolute(pt: TouchPoint, pressureDivisor: Float): Float {
        if (pt.pressure <= 0f) return 0.35f
        val norm = if (pressureDivisor <= 1.5f) {
            pt.pressure.coerceIn(0.01f, 1f)
        } else {
            (pt.pressure / pressureDivisor).coerceIn(0.01f, 1f)
        }
        return norm.pow(0.85f).coerceIn(0.01f, 1f)
    }

    private fun pressureToRadius(baseWidth: Float, signal: Float, style: HardwarePenStyle): Float {
        val (curve, minF, maxF) = when (style) {
            HardwarePenStyle.FOUNTAIN -> Triple(0.5f, 0.10f, 1.05f)
            else -> Triple(0.30f, 0.06f, 2.2f)
        }
        return max(1f, lerp(baseWidth * minF, baseWidth * maxF, signal.coerceIn(0f, 1f).pow(curve)))
    }

    // ─── Math helpers ─────────────────────────────────────────────────────────

    private fun lerp(a: Float, b: Float, t: Float) = a + (b - a) * t.coerceIn(0f, 1f)

    private fun withAlpha(color: Int, alpha: Int): Int =
        Color.argb(alpha.coerceIn(0, 255), Color.red(color), Color.green(color), Color.blue(color))

    /** Deterministic pseudo-random float in [0, 1) — same inputs → same dot positions. */
    private fun hashUnit(seed: Int, salt: Int): Float {
        var v = seed * 1103515245 + 12345 + salt * 374761393
        v = v xor (v ushr 16); v *= 668265263; v = v xor (v ushr 15)
        return (v ushr 1).toUInt().toFloat() / Int.MAX_VALUE.toFloat()
    }
}
