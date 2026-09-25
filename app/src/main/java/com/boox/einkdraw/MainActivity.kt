package com.boox.einkdraw

import android.app.Activity
import android.app.Dialog
import android.content.ClipData
import android.content.Intent
import android.graphics.Bitmap
import android.graphics.BitmapFactory
import android.graphics.Color
import android.graphics.ImageDecoder
import android.graphics.Matrix
import android.graphics.Rect
import android.graphics.drawable.ColorDrawable
import android.graphics.drawable.Drawable
import android.graphics.drawable.GradientDrawable
import android.graphics.drawable.LayerDrawable
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.provider.DocumentsContract
import android.provider.MediaStore
import android.provider.OpenableColumns
import android.text.SpannableStringBuilder
import android.text.Spanned
import android.text.method.LinkMovementMethod
import android.text.style.URLSpan
import android.util.Base64
import android.util.Log
import android.view.KeyEvent
import android.view.MotionEvent
import android.view.View
import android.widget.ImageButton
import android.widget.ImageView
import android.widget.LinearLayout
import android.widget.SeekBar
import android.widget.TextView
import android.widget.Toast
import androidx.activity.result.contract.ActivityResultContracts
import androidx.appcompat.app.AppCompatActivity
import androidx.core.content.FileProvider
import androidx.recyclerview.widget.ItemTouchHelper
import androidx.recyclerview.widget.LinearLayoutManager
import androidx.recyclerview.widget.RecyclerView
import com.onyx.android.sdk.api.device.epd.EpdController
import com.onyx.android.sdk.api.device.epd.UpdateMode
import org.json.JSONArray
import org.json.JSONObject
import java.io.ByteArrayOutputStream
import java.io.File
import java.io.FileOutputStream
import java.time.LocalDate
import kotlin.math.roundToInt
import kotlin.math.sqrt

class MainActivity : AppCompatActivity() {
    private enum class EraserExitCause {
        BRUSH_SELECTION,
        COLOR_SELECTION,
        OTHER,
    }

    companion object {
        private const val TAG = "MainActivity"
        private const val PREFS_NAME = "boox_einkdraw_prefs"
        private const val KEY_LAST_OPEN_URI = "last_open_uri"
        private const val KEY_BRUSH_STYLE = "brush_style"
        private const val KEY_BRUSH_WIDTHS = "brush_widths"
        private const val KEY_ERASER_WIDTH = "eraser_width"
        private const val KEY_INK_COLOR = "ink_color"
        private const val KEY_PICKER_COLOR = "picker_color"
        private const val KEY_VIEWPORT_LOCKED = "viewport_locked"
        private const val KEY_COLOR_HISTORY = "color_history"
        private const val MAX_COLOR_HISTORY = 6
        private const val AUTOSAVE_FILE_NAME = "autosave.json"
    }

    private lateinit var penView: HardwarePenSurfaceView
    private lateinit var rootFrame: View
    private lateinit var toolbarRow: View
    private lateinit var brushRow: LinearLayout
    private lateinit var widthSeekBar: SeekBar
    private lateinit var widthValueLabel: TextView
    private lateinit var zoomValueLabel: TextView
    private lateinit var swatchBlack: View
    private lateinit var swatchWhite: View
    private lateinit var swatchBlue: View
    private lateinit var colorPickerPanel: View
    private lateinit var colorPickerView: CircularColorPickerView
    private lateinit var colorHexValue: TextView
    private lateinit var grayscaleSeekBar: SeekBar
    private var grayscaleThumb: GradientDrawable? = null
    private lateinit var colorHistoryRow: LinearLayout
    private lateinit var layerPanel: View
    private lateinit var layerDragHandle: View
    private lateinit var layerRecycler: RecyclerView
    private lateinit var fileMenuPanel: View
    private lateinit var buttonLayers: ImageButton
    private lateinit var buttonMenu: ImageButton
    private lateinit var buttonEraser: ImageButton
    private lateinit var buttonUndo: ImageButton
    private lateinit var buttonRedo: ImageButton
    private lateinit var buttonAddLayer: ImageButton
    private lateinit var buttonRemoveLayer: ImageButton
    private lateinit var layerAdapter: LayerListAdapter

    private val brushButtons = LinkedHashMap<HardwarePenStyle, ImageButton>(HardwarePenStyle.entries.size)
    private val brushWidths = HardwarePenStyle.entries.associateWith { it.defaultWidthPx }.toMutableMap()
    private var eraserWidthPx: Float = 30f
    private var selectedBrushStyle: HardwarePenStyle = HardwarePenStyle.PENCIL
    private var selectedBrushBtn: ImageButton? = null
    private var selectedColorSwatch: View? = null
    private val recentColors = ArrayDeque<Int>()
    private var pickerInFlight: Boolean = false
    private var activityPaused: Boolean = false
    private var uiTouchDepth: Int = 0
    private var aboutDialogVisible: Boolean = false
    private var layerDragDx: Float = 0f
    private var layerDragDy: Float = 0f
    private var currentInkColor: Int = Color.BLACK
    private var pickerDotColor: Int = Color.BLUE
    private var viewportLocked: Boolean = false
    private var currentDocumentBaseName: String = defaultDocumentBaseName()
    private var manualEraserMode: Boolean = false
    private var lastBrushBeforeEraser: HardwarePenStyle? = null
    private var lastColorBeforeEraser: Int? = null
    private var eraserWasActive: Boolean = false
    private var pendingEraserExitCause: EraserExitCause = EraserExitCause.OTHER
    private var eraserUiTransitionInFlight: Boolean = false
    private var pendingEraserUiTransitionReset: Runnable? = null
    private var historyUiTransitionInFlight: Boolean = false
    private var pendingHistoryUiTransitionReset: Runnable? = null
    private var lastCanUndo: Boolean = false
    private var lastCanRedo: Boolean = false
    private var historyButtonActionInFlight: Boolean = false
    private var overlayDismissInFlight: Boolean = false
    private var pendingOverlayDismissReset: Runnable? = null
    private var consumingDismissGesture: Boolean = false
    private var pendingIncomingViewUri: Uri? = null
    private var pendingIncomingViewFlags: Int = 0
    private var pendingIncomingViewAttempts: Int = 0
    private val openMimeTypes = arrayOf("image/*", "application/json", "text/plain", "application/octet-stream")

    private val savePngLauncher = registerForActivityResult(
        ActivityResultContracts.CreateDocument("image/png")
    ) { uri ->
        uri?.let { savePng(it) }
        pickerInFlight = false
        updateRawSuppression()
    }

    private val saveDpaintLauncher = registerForActivityResult(
        ActivityResultContracts.CreateDocument("application/json")
    ) { uri ->
        uri?.let { saveDpaint(it) }
        pickerInFlight = false
        updateRawSuppression()
    }

    private val loadDocumentLauncher = registerForActivityResult(
        ActivityResultContracts.StartActivityForResult()
    ) { result ->
        val uri = if (result.resultCode == Activity.RESULT_OK) result.data?.data else null
        if (uri != null) {
            val flags = result.data?.flags ?: 0
            val readFlags = flags and (
                Intent.FLAG_GRANT_READ_URI_PERMISSION or
                    Intent.FLAG_GRANT_WRITE_URI_PERMISSION
                )
            runCatching { contentResolver.takePersistableUriPermission(uri, readFlags) }
            rememberLastOpenUri(uri)
            loadDocument(uri)
        }
        pickerInFlight = false
        updateRawSuppression()
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContentView(R.layout.activity_main)

        rootFrame = findViewById(R.id.rootFrame)
        toolbarRow = findViewById(R.id.toolbarRow)
        penView = findViewById(R.id.penSurfaceView)
        brushRow = findViewById(R.id.brushButtonRow)
        widthSeekBar = findViewById(R.id.widthSeekBar)
        widthValueLabel = findViewById(R.id.widthValueLabel)
        zoomValueLabel = findViewById(R.id.zoomValueLabel)
        swatchBlack = findViewById(R.id.swatchBlack)
        swatchWhite = findViewById(R.id.swatchWhite)
        swatchBlue = findViewById(R.id.swatchBlue)
        colorPickerPanel = findViewById(R.id.colorPickerPanel)
        colorPickerView = findViewById(R.id.colorPickerView)
        colorHexValue = findViewById(R.id.textColorHex)
        grayscaleSeekBar = findViewById(R.id.grayscaleSeekBar)
        colorHistoryRow = findViewById(R.id.colorHistoryRow)
        layerPanel = findViewById(R.id.layerPanel)
        layerDragHandle = findViewById(R.id.layerDragHandle)
        layerRecycler = findViewById(R.id.layerRecycler)
        fileMenuPanel = findViewById(R.id.fileMenuPanel)
        buttonLayers = findViewById(R.id.buttonLayers)
        buttonMenu = findViewById(R.id.buttonMenu)
        buttonEraser = findViewById(R.id.buttonEraser)
        buttonUndo = findViewById(R.id.buttonUndo)
        buttonRedo = findViewById(R.id.buttonRedo)
        buttonAddLayer = findViewById(R.id.buttonAddLayer)
        buttonRemoveLayer = findViewById(R.id.buttonRemoveLayer)

        val loadBtn = findViewById<View>(R.id.buttonLoad)
        val clearLayerBtn = findViewById<View>(R.id.buttonClearLayer)
        val clearFileBtn = findViewById<View>(R.id.buttonClearFile)
        val saveBtn = findViewById<View>(R.id.buttonSave)
        val saveFileBtn = findViewById<View>(R.id.buttonSaveFile)
        val shareBtn = findViewById<View>(R.id.buttonShare)
        val resetViewBtn = findViewById<View>(R.id.buttonResetView)
        val lockViewportBtn = findViewById<TextView>(R.id.buttonLockViewport)
        val aboutBtn = findViewById<View>(R.id.buttonAbout)

        loadToolbarPrefs()
        setupBrushButtons()
        setupWidthSeekBar()
        setupColorPickerPanel()
        setupGrayscaleSlider()
        setupColorSwatches()
        setupLayerPanel()
        setupLayerPanelDrag()
        penView.setOnViewportChangedListener { scale ->
            runOnUiThread { updateZoomLabel(scale) }
        }
        zoomValueLabel.setOnClickListener { resetViewport() }

        guardRawMode(widthSeekBar)
        guardRawMode(grayscaleSeekBar)
        guardRawMode(zoomValueLabel)
        guardRawMode(loadBtn)
        guardRawMode(clearLayerBtn)
        guardRawMode(clearFileBtn)
        guardRawMode(saveBtn)
        guardRawMode(saveFileBtn)
        guardRawMode(shareBtn)
        guardRawMode(resetViewBtn)
        guardRawMode(lockViewportBtn)
        guardRawMode(aboutBtn)
        guardRawMode(swatchBlack)
        guardRawMode(swatchWhite)
        guardRawMode(swatchBlue)
        guardRawMode(buttonLayers)
        guardRawMode(buttonEraser)
        guardRawMode(buttonUndo)
        guardRawMode(buttonRedo)
        guardRawMode(buttonAddLayer)
        guardRawMode(buttonRemoveLayer)
        guardRawMode(layerRecycler)
        guardRawMode(fileMenuPanel)
        guardRawMode(colorPickerPanel)
        guardRawMode(colorPickerView)

        loadBtn.setOnClickListener {
            fileMenuPanel.visibility = View.GONE
            pickerInFlight = true
            updateRawSuppression()
            loadDocumentLauncher.launch(buildOpenDocumentIntent())
        }
        clearLayerBtn.setOnClickListener {
            fileMenuPanel.visibility = View.GONE
            val ok = penView.clearCurrentLayer()
            if (!ok) {
                Toast.makeText(this, "No active layer", Toast.LENGTH_SHORT).show()
            }
            refreshLayerPanel()
            updateRawSuppression()
        }
        clearFileBtn.setOnClickListener {
            fileMenuPanel.visibility = View.GONE
            penView.clearFile()
            currentDocumentBaseName = defaultDocumentBaseName()
            refreshLayerPanel()
            updateRawSuppression()
        }
        saveBtn.setOnClickListener {
            fileMenuPanel.visibility = View.GONE
            pickerInFlight = true
            updateRawSuppression()
            savePngLauncher.launch("${currentDocumentBaseName}.png")
        }
        saveFileBtn.setOnClickListener {
            fileMenuPanel.visibility = View.GONE
            pickerInFlight = true
            updateRawSuppression()
            saveDpaintLauncher.launch("${currentDocumentBaseName}.json")
        }
        shareBtn.setOnClickListener {
            fileMenuPanel.visibility = View.GONE
            sharePng()
            updateRawSuppression()
        }
        resetViewBtn.setOnClickListener {
            fileMenuPanel.visibility = View.GONE
            resetViewport()
            updateRawSuppression()
        }
        lockViewportBtn.setOnClickListener {
            viewportLocked = !viewportLocked
            penView.setViewportLocked(viewportLocked)
            updateLockViewportLabel(lockViewportBtn)
        }
        penView.setViewportLocked(viewportLocked)
        updateLockViewportLabel(lockViewportBtn)
        aboutBtn.setOnClickListener {
            fileMenuPanel.visibility = View.GONE
            showAboutDialog()
        }
        buttonLayers.setOnClickListener { toggleLayerPanel() }
        bindImmediateDownAction(buttonMenu) { toggleFileMenu() }
        buttonEraser.setOnClickListener { toggleManualEraserMode() }
        buttonUndo.setOnClickListener { historyButtonActionInFlight = true; penView.undo() }
        buttonRedo.setOnClickListener { historyButtonActionInFlight = true; penView.redo() }
        // History starts empty; set the disabled visuals up front so the initial listener invoke is
        // a no-op and does not run a spurious toolbar refresh at launch.
        buttonUndo.isEnabled = false
        buttonUndo.alpha = 0.3f
        buttonRedo.isEnabled = false
        buttonRedo.alpha = 0.3f
        penView.setOnHistoryChangedListener {
            runOnUiThread { updateUndoRedoButtons() }
        }
        penView.setOnStrokeIntentListener {
            runOnUiThread { cancelHistoryUiTransition() }
        }
        penView.setOnEraserModeChangedListener { active ->
            runOnUiThread { applyEraserModeUiTransition(active) }
        }
        penView.setOnStylusHoverButtonChangedListener { state ->
            Log.i(
                TAG,
                "stylusHoverButtons hovering=${state.hovering} primary=${state.stylusPrimaryPressed} " +
                    "secondary=${state.stylusSecondaryPressed} raw=0x${state.buttonState.toString(16)}"
            )
        }

        selectBrush(selectedBrushStyle)
        refreshLayerPanel()
        ensureOverlayOrder()
        updateRawSuppression()
        updateZoomLabel(penView.getViewScale())
        handleIncomingViewIntent(intent)
        restoreAutosaveWhenReady()
    }

    override fun onNewIntent(intent: Intent) {
        super.onNewIntent(intent)
        setIntent(intent)
        handleIncomingViewIntent(intent)
    }

    private fun setupBrushButtons() {
        HardwarePenStyle.entries.forEach { style ->
            val btn = ImageButton(this).apply {
                setImageResource(brushIconRes(style))
                background = null
                setPadding(dp(1), dp(1), dp(1), dp(1))
                scaleType = ImageView.ScaleType.MATRIX
                contentDescription = style.label
                alpha = 0.45f
                setOnClickListener { selectBrush(style) }
            }
            updateBrushIconTransform(btn, selected = false)
            guardRawMode(btn)
            brushButtons[style] = btn
            brushRow.addView(
                btn,
                LinearLayout.LayoutParams(
                    dp(24),
                    dp(30)
                ).also { it.marginEnd = dp(1) }
            )
        }
    }

    private fun brushIconRes(style: HardwarePenStyle): Int = when (style) {
        HardwarePenStyle.PENCIL -> R.drawable.ic_brush_pencil_tip
        HardwarePenStyle.FOUNTAIN -> R.drawable.ic_brush_fountain_tip
        HardwarePenStyle.MARKER -> R.drawable.ic_brush_marker_tip
        HardwarePenStyle.NEO_BRUSH -> R.drawable.ic_brush_neo_tip
        HardwarePenStyle.CHARCOAL -> R.drawable.ic_brush_charcoal_tip
        HardwarePenStyle.DASH -> R.drawable.ic_brush_dash_tip
        HardwarePenStyle.CHARCOAL_V2 -> R.drawable.ic_brush_charcoal_v2_tip
        HardwarePenStyle.SQUARE_PEN -> R.drawable.ic_brush_square_tip
    }

    private fun setupLayerPanel() {
        layerAdapter = LayerListAdapter(
            onSelect = { layerId ->
                if (penView.setActiveLayer(layerId)) refreshLayerPanel()
            },
            onToggleVisible = { layerId, visible ->
                if (penView.setLayerVisible(layerId, visible)) refreshLayerPanel()
            },
            onOpacityChanged = { layerId, opacity ->
                penView.setLayerOpacity(layerId, opacity)
            }
        )
        layerRecycler.layoutManager = LinearLayoutManager(this)
        layerRecycler.adapter = layerAdapter

        val itemTouchHelper = ItemTouchHelper(object : ItemTouchHelper.SimpleCallback(
            ItemTouchHelper.UP or ItemTouchHelper.DOWN,
            0
        ) {
            override fun onMove(
                recyclerView: RecyclerView,
                viewHolder: RecyclerView.ViewHolder,
                target: RecyclerView.ViewHolder
            ): Boolean {
                val from = viewHolder.bindingAdapterPosition
                val to = target.bindingAdapterPosition
                if (from == RecyclerView.NO_POSITION || to == RecyclerView.NO_POSITION) return false
                layerAdapter.moveItem(from, to)
                penView.moveLayerByDisplayIndices(from, to)
                return true
            }

            override fun onSwiped(viewHolder: RecyclerView.ViewHolder, direction: Int) = Unit

            override fun clearView(recyclerView: RecyclerView, viewHolder: RecyclerView.ViewHolder) {
                super.clearView(recyclerView, viewHolder)
                refreshLayerPanel()
            }
        })
        itemTouchHelper.attachToRecyclerView(layerRecycler)

        buttonAddLayer.setOnClickListener {
            penView.addLayer()
            refreshLayerPanel()
        }
        buttonRemoveLayer.setOnClickListener {
            val active = penView.getLayerInfos().firstOrNull { it.active }
            if (active == null) {
                Toast.makeText(this, "No active layer", Toast.LENGTH_SHORT).show()
                return@setOnClickListener
            }
            val removed = penView.removeLayer(active.id)
            if (!removed) {
                Toast.makeText(this, "Cannot remove last layer", Toast.LENGTH_SHORT).show()
            }
            refreshLayerPanel()
        }
    }

    private fun setupLayerPanelDrag() {
        layerDragHandle.setOnTouchListener { _, event ->
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    beginUiTouch()
                    layerDragDx = layerPanel.x - event.rawX
                    layerDragDy = layerPanel.y - event.rawY
                    true
                }

                MotionEvent.ACTION_MOVE -> {
                    moveLayerPanel(event.rawX + layerDragDx, event.rawY + layerDragDy)
                    true
                }

                MotionEvent.ACTION_UP -> {
                    endUiTouch(false)
                    true
                }

                MotionEvent.ACTION_CANCEL -> {
                    endUiTouch(true)
                    true
                }

                else -> false
            }
        }
    }

    private fun moveLayerPanel(targetX: Float, targetY: Float) {
        val parentW = rootFrame.width
        val parentH = rootFrame.height
        if (parentW <= 0 || parentH <= 0) return
        val maxX = (parentW - layerPanel.width).coerceAtLeast(0)
        val maxY = (parentH - layerPanel.height).coerceAtLeast(0)
        layerPanel.x = targetX.coerceIn(0f, maxX.toFloat())
        layerPanel.y = targetY.coerceIn(0f, maxY.toFloat())
        ensureOverlayOrder()
    }

    private fun toggleLayerPanel() {
        val willShow = layerPanel.visibility != View.VISIBLE
        if (willShow) {
            colorPickerPanel.visibility = View.GONE
            refreshPickerToggleSwatch(active = false)
        }
        layerPanel.visibility = if (willShow) View.VISIBLE else View.GONE
        if (willShow) refreshLayerPanel()
        ensureOverlayOrder()
        if (!willShow) overlayDismissInFlight = true
        updateRawSuppression()
        if (!willShow) refreshUiAfterOverlayDismiss()
    }

    private fun toggleColorPickerPanel() {
        val willShow = colorPickerPanel.visibility != View.VISIBLE
        if (willShow) {
            layerPanel.visibility = View.GONE
            colorPickerView.setColor(pickerDotColor)
            colorHexValue.text = formatHex(pickerDotColor)
        }
        colorPickerPanel.visibility = if (willShow) View.VISIBLE else View.GONE
        if (!willShow) onColorPickerPanelClosed()
        refreshPickerToggleSwatch(active = willShow)
        ensureOverlayOrder()
        if (!willShow) overlayDismissInFlight = true
        updateRawSuppression()
        if (!willShow) refreshUiAfterOverlayDismiss()
    }

    private fun toggleFileMenu() {
        val willShow = fileMenuPanel.visibility != View.VISIBLE
        fileMenuPanel.visibility = if (willShow) View.VISIBLE else View.GONE
        ensureOverlayOrder()
        if (!willShow) overlayDismissInFlight = true
        updateRawSuppression()
        if (!willShow) refreshUiAfterOverlayDismiss()
    }

    private fun ensureOverlayOrder() {
        layerPanel.bringToFront()
        colorPickerPanel.bringToFront()
        fileMenuPanel.bringToFront()
    }

    private fun refreshLayerPanel() {
        layerAdapter.submit(penView.getLayerInfos())
    }

    private fun selectBrush(style: HardwarePenStyle) {
        if (penView.isEraseModeActive()) {
            pendingEraserExitCause = EraserExitCause.BRUSH_SELECTION
            manualEraserMode = false
            penView.deactivateEraserMode()
        }
        applyBrushSelection(style)
    }

    private fun applyBrushSelection(style: HardwarePenStyle) {
        selectedBrushStyle = style
        penView.setStyle(style)
        val width = brushWidths[style] ?: style.defaultWidthPx
        penView.setStrokeWidthPx(width)
        widthSeekBar.progress = widthToProgress(width)
        widthValueLabel.text = "${width.roundToInt()} px"

        selectedBrushBtn = brushButtons[style]
        refreshToolVisuals(penView.isEraseModeActive())
    }

    private fun applyEraserWidth() {
        penView.setStrokeWidthPx(eraserWidthPx)
        widthSeekBar.progress = widthToProgress(eraserWidthPx)
        widthValueLabel.text = "${eraserWidthPx.roundToInt()} px"
    }

    private fun toggleManualEraserMode() {
        if (!manualEraserMode) {
            manualEraserMode = true
            pendingEraserExitCause = EraserExitCause.OTHER
            penView.setManualEraserMode(true)
            return
        }

        pendingEraserExitCause = EraserExitCause.OTHER
        manualEraserMode = false
        penView.setManualEraserMode(false)
    }

    private fun updateUndoRedoButtons() {
        val canUndo = penView.canUndo()
        val canRedo = penView.canRedo()
        // Only touch the toolbar when a button's enabled state actually flips; otherwise the
        // refresh/pause runs on every stroke and just flickers the panel.
        if (canUndo == lastCanUndo && canRedo == lastCanRedo) return
        lastCanUndo = canUndo
        lastCanRedo = canRedo
        buttonUndo.isEnabled = canUndo
        buttonUndo.alpha = if (canUndo) 1f else 0.3f
        buttonRedo.isEnabled = canRedo
        buttonRedo.alpha = if (canRedo) 1f else 0.3f
        // Undo/redo button taps already repaint the canvas via applyPatch; refresh the toolbar
        // once in the same cycle (no pause/delay) so it coalesces instead of flashing twice.
        if (historyButtonActionInFlight) {
            historyButtonActionInFlight = false
            refreshToolbarEinkImmediately()
            return
        }
        // Stroke end: raw drawing holds the e-ink panel and swallows toolbar refreshes, so pause it
        // briefly (like the eraser transition) to let the button state repaint, then re-enable it.
        historyUiTransitionInFlight = true
        updateRawSuppression()
        // Raw drawing is disabled asynchronously on the helper thread, so refresh once after a
        // short delay to ensure it has landed; refreshing sooner gets swallowed.
        rootFrame.postDelayed({ refreshToolbarEinkImmediately() }, 80L)
        pendingHistoryUiTransitionReset?.let { rootFrame.removeCallbacks(it) }
        val reset = Runnable {
            historyUiTransitionInFlight = false
            updateRawSuppression()
        }
        pendingHistoryUiTransitionReset = reset
        rootFrame.postDelayed(reset, 250L)
    }

    /** End the history refresh pause early so a new stroke is not blocked by suppressed raw input. */
    private fun cancelHistoryUiTransition() {
        if (!historyUiTransitionInFlight) return
        pendingHistoryUiTransitionReset?.let { rootFrame.removeCallbacks(it) }
        pendingHistoryUiTransitionReset = null
        historyUiTransitionInFlight = false
        updateRawSuppression()
    }

    private fun refreshToolVisuals(eraseActive: Boolean) {
        brushButtons.forEach { (style, btn) ->
            val selected = !eraseActive && style == selectedBrushStyle
            btn.alpha = if (selected) 1f else 0.45f
            btn.translationY = if (selected) dp(3).toFloat() else 0f
            updateBrushIconTransform(btn, selected = selected)
        }
        updateEraserButtonVisual(eraseActive)
    }

    private fun updateEraserButtonVisual(active: Boolean) {
        buttonEraser.alpha = if (active) 1f else 0.45f
        buttonEraser.translationY = if (active) dp(3).toFloat() else 0f
    }

    private fun updateBrushIconTransform(button: ImageButton, selected: Boolean) {
        val shiftY = if (selected) dpF(-7f) else dpF(-10f)
        button.imageMatrix = Matrix().apply { setTranslate(0f, shiftY) }
    }

    private fun setupWidthSeekBar() {
        widthSeekBar.setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
            override fun onProgressChanged(sb: SeekBar, progress: Int, fromUser: Boolean) {
                if (!fromUser) return
                val width = progressToWidth(progress)
                widthValueLabel.text = "${width.roundToInt()} px"
                if (penView.isEraseModeActive()) {
                    eraserWidthPx = width
                } else {
                    brushWidths[selectedBrushStyle] = width
                }
                penView.setStrokeWidthPx(width)
            }

            override fun onStartTrackingTouch(sb: SeekBar) = Unit
            override fun onStopTrackingTouch(sb: SeekBar) = Unit
        })
    }

    private fun setupGrayscaleSlider() {
        val gradient = GradientDrawable(
            GradientDrawable.Orientation.LEFT_RIGHT,
            intArrayOf(Color.BLACK, Color.WHITE)
        ).apply {
            cornerRadius = dpF(7f)
            setStroke(dp(1), Color.LTGRAY)
            setSize(0, dp(14))
        }
        val track = LayerDrawable(arrayOf<Drawable>(gradient, ColorDrawable(Color.TRANSPARENT))).apply {
            setId(0, android.R.id.background)
            setId(1, android.R.id.progress)
        }
        grayscaleSeekBar.progressDrawable = track
        val thumb = GradientDrawable().apply {
            shape = GradientDrawable.OVAL
            setColor(currentInkColor)
            setStroke(dp(2), Color.WHITE)
            setSize(dp(22), dp(22))
        }
        grayscaleThumb = thumb
        grayscaleSeekBar.thumb = thumb
        grayscaleSeekBar.setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
            override fun onProgressChanged(sb: SeekBar, progress: Int, fromUser: Boolean) {
                if (!fromUser) return
                applyColor(Color.rgb(progress, progress, progress), swatch = null, syncPicker = true)
            }

            override fun onStartTrackingTouch(sb: SeekBar) = Unit
            override fun onStopTrackingTouch(sb: SeekBar) = Unit
        })
    }

    private fun setupColorPickerPanel() {
        colorPickerView.onColorChanged = { color ->
            applyColor(color, swatch = null, syncPicker = false)
        }
        colorHexValue.text = formatHex(currentInkColor)
        colorPickerView.setColor(pickerDotColor)
        refreshColorHistoryRow()
    }

    /** Record the last picker color into history when the picker panel closes. */
    private fun onColorPickerPanelClosed() {
        recentColors.removeAll { it == pickerDotColor }
        recentColors.addFirst(pickerDotColor)
        while (recentColors.size > MAX_COLOR_HISTORY) recentColors.removeLast()
        refreshColorHistoryRow()
    }

    /** Rebuild the history swatch dots from the current recentColors list. */
    private fun refreshColorHistoryRow() {
        colorHistoryRow.removeAllViews()
        val size = dp(28)
        val margin = dp(3)
        recentColors.forEach { color ->
            val dot = View(this).apply {
                layoutParams = LinearLayout.LayoutParams(size, size).apply {
                    marginStart = margin
                    marginEnd = margin
                }
                background = createSwatchDrawable(color, selected = false)
                setOnClickListener { applyColor(color, swatch = null, syncPicker = true) }
            }
            guardRawMode(dot)
            colorHistoryRow.addView(dot)
        }
    }

    private fun setupColorSwatches() {
        bindColorSwatch(swatchBlack, Color.BLACK)
        bindColorSwatch(swatchWhite, Color.WHITE)
        swatchBlue.setOnClickListener { toggleColorPickerPanel() }
        refreshPickerToggleSwatch(active = false)
        val initialSwatch = when (currentInkColor) {
            Color.BLACK -> swatchBlack
            Color.WHITE -> swatchWhite
            else -> null
        }
        applyColor(currentInkColor, swatch = initialSwatch, syncPicker = false)
    }

    private fun bindColorSwatch(swatch: View, color: Int) {
        swatch.setOnClickListener { applyColor(color, swatch, syncPicker = true) }
        swatch.background = createSwatchDrawable(color, selected = false)
    }

    private fun applyColor(color: Int, swatch: View?, syncPicker: Boolean) {
        if (penView.isEraseModeActive()) {
            pendingEraserExitCause = EraserExitCause.COLOR_SELECTION
            manualEraserMode = false
            penView.deactivateEraserMode()
        }
        currentInkColor = Color.rgb(Color.red(color), Color.green(color), Color.blue(color))
        penView.setStrokeColor(color)
        val previous = selectedColorSwatch
        previous?.background = createSwatchDrawable(selectedInkColorOf(previous), selected = false)
        if (swatch != null) {
            swatch.background = createSwatchDrawable(selectedInkColorOf(swatch), selected = true)
        }
        selectedColorSwatch = swatch
        if (swatch == null) {
            pickerDotColor = currentInkColor
        }
        colorHexValue.text = formatHex(currentInkColor)
        val luma = (0.299f * Color.red(currentInkColor) +
            0.587f * Color.green(currentInkColor) +
            0.114f * Color.blue(currentInkColor)).roundToInt().coerceIn(0, 255)
        grayscaleSeekBar.progress = luma
        grayscaleThumb?.setColor(Color.rgb(luma, luma, luma))
        refreshPickerToggleSwatch(active = colorPickerPanel.visibility == View.VISIBLE)
        if (syncPicker) {
            colorPickerView.setColor(currentInkColor)
        }
    }

    private fun onEraserModeChanged(active: Boolean) {
        if (active == eraserWasActive) return
        if (active) {
            lastBrushBeforeEraser = selectedBrushStyle
            lastColorBeforeEraser = currentInkColor
            pendingEraserExitCause = EraserExitCause.OTHER
            eraserWasActive = true
            applyEraserWidth()
            return
        }

        val exitCause = pendingEraserExitCause
        pendingEraserExitCause = EraserExitCause.OTHER
        manualEraserMode = false

        if (exitCause != EraserExitCause.BRUSH_SELECTION) {
            val restoreBrush = lastBrushBeforeEraser ?: selectedBrushStyle
            applyBrushSelection(restoreBrush)
        }
        if (exitCause != EraserExitCause.COLOR_SELECTION) {
            val restoreColor = lastColorBeforeEraser
            if (restoreColor != null) {
                val restoreSwatch = when (restoreColor) {
                    Color.BLACK -> swatchBlack
                    Color.WHITE -> swatchWhite
                    else -> null
                }
                applyColor(restoreColor, swatch = restoreSwatch, syncPicker = true)
            }
        }
        eraserWasActive = false
    }

    private fun applyEraserModeUiTransition(active: Boolean) {
        // Force a short pause of hardware preview so toolbar state changes become visible immediately on e-ink.
        eraserUiTransitionInFlight = true
        updateRawSuppression()

        onEraserModeChanged(active)
        refreshToolVisuals(active)
        refreshToolbarEinkImmediately()
        rootFrame.postDelayed({ refreshToolbarEinkImmediately() }, 16L)

        pendingEraserUiTransitionReset?.let { rootFrame.removeCallbacks(it) }
        val reset = Runnable {
            eraserUiTransitionInFlight = false
            updateRawSuppression()
        }
        pendingEraserUiTransitionReset = reset
        rootFrame.postDelayed(reset, 48L)
    }

    private fun selectedInkColorOf(swatch: View?): Int = when (swatch?.id) {
        R.id.swatchWhite -> Color.WHITE
        else -> Color.BLACK
    }

    private fun createSwatchDrawable(fill: Int, selected: Boolean): GradientDrawable {
        val ringColor = when {
            selected && fill == Color.WHITE -> Color.BLACK
            selected -> Color.WHITE
            fill == Color.WHITE -> Color.DKGRAY
            else -> Color.LTGRAY
        }
        return GradientDrawable().apply {
            shape = GradientDrawable.OVAL
            setColor(fill)
            setStroke(if (selected) dp(2) else dp(1), ringColor)
        }
    }

    private fun createPickerToggleDrawable(active: Boolean, fillColor: Int): GradientDrawable {
        return GradientDrawable().apply {
            shape = GradientDrawable.OVAL
            setColor(fillColor)
            setStroke(if (active) dp(2) else dp(1), if (active) Color.WHITE else Color.LTGRAY)
        }
    }

    private fun refreshPickerToggleSwatch(active: Boolean) {
        swatchBlue.background = createPickerToggleDrawable(active = active, fillColor = pickerDotColor)
    }

    private fun formatHex(color: Int): String =
        String.format("#%02X%02X%02X", Color.red(color), Color.green(color), Color.blue(color))

    private fun refreshToolbarEinkImmediately() {
        toolbarRow.invalidate()
        brushRow.invalidate()
        buttonEraser.invalidate()
        rootFrame.invalidate()
        val decor = window?.decorView ?: rootFrame
        rootFrame.post {
            runCatching {
                // Use a regular UI refresh mode here; handwriting mode often skips toolbar-only changes.
                EpdController.invalidate(toolbarRow, UpdateMode.GU)
                EpdController.refreshScreen(toolbarRow, UpdateMode.GU)
                EpdController.invalidate(decor, UpdateMode.GU)
                EpdController.refreshScreen(decor, UpdateMode.GU)
            }
        }
    }

    private fun progressToWidth(progress: Int): Float {
        val t = progress / 99f
        return 1f + t * t * 79f
    }

    private fun updateZoomLabel(scale: Float) {
        val pct = (scale * 100f).roundToInt().coerceAtLeast(100)
        zoomValueLabel.text = "${pct}%"
    }

    private fun resetViewport() {
        penView.resetViewport()
        updateZoomLabel(penView.getViewScale())
    }

    private fun widthToProgress(width: Float): Int {
        val t = ((width - 1f) / 79f).coerceIn(0f, 1f)
        return (sqrt(t.toDouble()) * 99).roundToInt()
    }

    private fun savePng(uri: Uri) {
        val bmp = penView.exportBitmap() ?: run {
            Toast.makeText(this, "Nothing to save", Toast.LENGTH_SHORT).show()
            return
        }
        val ok = runCatching {
            contentResolver.openOutputStream(uri, "w")?.use {
                bmp.compress(android.graphics.Bitmap.CompressFormat.PNG, 100, it)
            } ?: false
        }.getOrDefault(false)
        Toast.makeText(this, if (ok) "Exported" else "Export failed", Toast.LENGTH_SHORT).show()
    }

    private fun saveDpaint(uri: Uri) {
        val snapshot = penView.snapshotDocumentForExport() ?: run {
            Toast.makeText(this, "Nothing to save", Toast.LENGTH_SHORT).show()
            return
        }
        val name = documentDisplayName(uri)?.substringBeforeLast('.')?.ifBlank { "Untitled" } ?: "Untitled"
        val ok = runCatching {
            val json = buildDpaintJson(snapshot, name)
            contentResolver.openOutputStream(uri, "w")?.use { out ->
                out.write(json.toString().toByteArray(Charsets.UTF_8))
                true
            } ?: false
        }.getOrDefault(false)
        snapshot.layers.forEach { if (!it.bitmap.isRecycled) it.bitmap.recycle() }
        if (ok) {
            currentDocumentBaseName = normalizeDocumentBaseName(documentDisplayName(uri))
        }
        Toast.makeText(this, if (ok) "Saved" else "Save failed", Toast.LENGTH_SHORT).show()
    }

    private fun sharePng() {
        val bmp = penView.exportBitmap() ?: run {
            Toast.makeText(this, "Nothing to share", Toast.LENGTH_SHORT).show()
            return
        }

        val safeName = normalizeDocumentBaseName(currentDocumentBaseName)
        val sharedDir = File(cacheDir, "shared")
        if (!sharedDir.exists() && !sharedDir.mkdirs()) {
            Toast.makeText(this, "Share failed", Toast.LENGTH_SHORT).show()
            return
        }

        val target = File(sharedDir, "$safeName.png")
        val ok = runCatching {
            FileOutputStream(target).use { out ->
                bmp.compress(Bitmap.CompressFormat.PNG, 100, out)
            }
            true
        }.getOrDefault(false)
        if (!ok) {
            Toast.makeText(this, "Share failed", Toast.LENGTH_SHORT).show()
            return
        }

        val uri = runCatching {
            FileProvider.getUriForFile(this, "$packageName.fileprovider", target)
        }.getOrNull()
        if (uri == null) {
            Toast.makeText(this, "Share failed", Toast.LENGTH_SHORT).show()
            return
        }

        val sendIntent = Intent(Intent.ACTION_SEND).apply {
            type = "image/png"
            putExtra(Intent.EXTRA_STREAM, uri)
            putExtra(Intent.EXTRA_SUBJECT, safeName)
            putExtra(Intent.EXTRA_TITLE, safeName)
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
            clipData = ClipData.newUri(contentResolver, "$safeName.png", uri)
        }
        val chooser = Intent.createChooser(sendIntent, "Share drawing")
        startActivity(chooser)
    }

    private fun loadDocument(uri: Uri) {
        val mime = contentResolver.getType(uri)?.lowercase().orEmpty()
        val name = documentDisplayName(uri)?.lowercase().orEmpty()
        val looksJson = mime.contains("json") || name.endsWith(".json")
        val looksImage = mime.startsWith("image/") ||
            name.endsWith(".png") || name.endsWith(".jpg") ||
            name.endsWith(".jpeg") || name.endsWith(".webp")

        if (looksJson) {
            val ok = loadDpaintDocument(uri)
            if (ok) {
                currentDocumentBaseName = normalizeDocumentBaseName(documentDisplayName(uri))
            }
            Toast.makeText(this, if (ok) "Loaded" else "Load failed", Toast.LENGTH_SHORT).show()
            return
        }

        if (looksImage) {
            val ok = loadImageIntoCurrentLayer(uri)
            if (ok) {
                currentDocumentBaseName = normalizeDocumentBaseName(documentDisplayName(uri))
            }
            Toast.makeText(this, if (ok) "Loaded" else "Load failed", Toast.LENGTH_SHORT).show()
            return
        }

        val loadedDpaint = loadDpaintDocument(uri)
        if (loadedDpaint) {
            currentDocumentBaseName = normalizeDocumentBaseName(documentDisplayName(uri))
            Toast.makeText(this, "Loaded", Toast.LENGTH_SHORT).show()
            return
        }
        val loadedImage = loadImageIntoCurrentLayer(uri)
        if (loadedImage) {
            currentDocumentBaseName = normalizeDocumentBaseName(documentDisplayName(uri))
        }
        Toast.makeText(this, if (loadedImage) "Loaded" else "Load failed", Toast.LENGTH_SHORT).show()
    }

    private fun handleIncomingViewIntent(incoming: Intent?) {
        val action = incoming?.action ?: return
        if (action != Intent.ACTION_VIEW) return
        val uri = incoming.data ?: return
        pendingIncomingViewUri = uri
        pendingIncomingViewFlags = incoming.flags
        pendingIncomingViewAttempts = 0
        processPendingIncomingViewIntent()
    }

    private fun processPendingIncomingViewIntent() {
        val uri = pendingIncomingViewUri ?: return
        if (penView.width <= 0 || penView.height <= 0) {
            if (pendingIncomingViewAttempts >= 40) {
                Log.w(TAG, "Incoming VIEW uri dropped: pen surface never became ready: $uri")
                pendingIncomingViewUri = null
                pendingIncomingViewFlags = 0
                pendingIncomingViewAttempts = 0
                Toast.makeText(this, "Load failed", Toast.LENGTH_SHORT).show()
                return
            }
            pendingIncomingViewAttempts += 1
            penView.postDelayed({ processPendingIncomingViewIntent() }, 32L)
            return
        }

        val flags = pendingIncomingViewFlags
        pendingIncomingViewUri = null
        pendingIncomingViewFlags = 0
        pendingIncomingViewAttempts = 0

        val readFlags = flags and (
            Intent.FLAG_GRANT_READ_URI_PERMISSION or
                Intent.FLAG_GRANT_WRITE_URI_PERMISSION
            )
        runCatching { contentResolver.takePersistableUriPermission(uri, readFlags) }

        rememberLastOpenUri(uri)
        loadDocument(uri)
    }

    private fun loadImageIntoCurrentLayer(uri: Uri): Boolean {
        val bitmap = runCatching {
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.P) {
                val source = ImageDecoder.createSource(contentResolver, uri)
                ImageDecoder.decodeBitmap(source) { decoder, _, _ ->
                    decoder.allocator = ImageDecoder.ALLOCATOR_SOFTWARE
                }
            } else {
                @Suppress("DEPRECATION")
                MediaStore.Images.Media.getBitmap(contentResolver, uri)
            }
        }.getOrNull()

        if (bitmap == null) return false
        val ok = penView.loadCanvasBitmap(bitmap)
        bitmap.recycle()
        if (ok) refreshLayerPanel()
        return ok
    }

    private fun loadDpaintDocument(uri: Uri): Boolean {
        val text = readUriText(uri) ?: return false
        return loadDpaintFromText(text)
    }

    private fun loadDpaintFromText(text: String): Boolean {
        val root = runCatching { JSONObject(text) }.getOrNull() ?: return false
        if (!root.optString("type").equals("dpaint", ignoreCase = true)) return false

        val image = root.optJSONObject("image") ?: return false
        val sourceWidth = image.optInt("width", 0)
        val sourceHeight = image.optInt("height", 0)
        val frames = image.optJSONArray("frames") ?: return false
        if (frames.length() <= 0) return false

        val frame = frames.optJSONObject(0) ?: return false
        val imageActiveIndex = image.optInt("activeLayerIndex", 0)
        val requestedActiveIndex = frame.optInt("activeLayerIndex", imageActiveIndex).coerceAtLeast(0)
        val layers = frame.optJSONArray("layers") ?: return false
        if (layers.length() <= 0) return false

        val importedLayers = ArrayList<HardwarePenSurfaceView.LayerSnapshot>(layers.length())
        var mappedActiveIndex = 0
        for (i in 0 until layers.length()) {
            val layerObj = layers.optJSONObject(i) ?: continue
            val canvasData = layerObj.optString("canvas", "")
            if (canvasData.isBlank()) continue
            val bitmap = decodeDataUrlBitmap(canvasData) ?: continue
            importedLayers.add(
                HardwarePenSurfaceView.LayerSnapshot(
                    name = layerObj.optString("name", "Layer ${i + 1}"),
                    visible = layerObj.optBoolean("visible", true),
                    opacity = (layerObj.optDouble("opacity", 100.0) / 100.0).toFloat(),
                    bitmap = bitmap,
                )
            )
            if (i == requestedActiveIndex) {
                mappedActiveIndex = importedLayers.lastIndex
            }
        }

        if (importedLayers.isEmpty()) return false
        val ok = penView.replaceFileWithLayers(
            sourceWidth = sourceWidth,
            sourceHeight = sourceHeight,
            sourceLayers = importedLayers,
            activeLayerIndex = mappedActiveIndex,
        )
        importedLayers.forEach { if (!it.bitmap.isRecycled) it.bitmap.recycle() }
        if (ok) {
            refreshLayerPanel()
            resetViewport()
        }
        return ok
    }

    private fun buildDpaintJson(
        snapshot: HardwarePenSurfaceView.DocumentSnapshot,
        imageName: String,
    ): JSONObject {
        val layersArray = JSONArray()
        snapshot.layers.forEach { layer ->
            layersArray.put(
                JSONObject()
                    .put("name", layer.name)
                    .put("blendMode", "normal")
                    .put("opacity", (layer.opacity.coerceIn(0f, 1f) * 100f).roundToInt().coerceIn(0, 100))
                    .put("visible", layer.visible)
                    .put("hasMask", false)
                    .put("canvas", bitmapToDataUrl(layer.bitmap))
            )
        }

        val frame = JSONObject()
            .put("activeLayerIndex", snapshot.activeLayerIndex)
            .put("layers", layersArray)

        val image = JSONObject()
            .put("name", imageName)
            .put("width", snapshot.width)
            .put("height", snapshot.height)
            .put("activeLayerIndex", snapshot.activeLayerIndex)
            .put("activeFrameIndex", 0)
            .put("frames", JSONArray().put(frame))
            .put("colorRange", JSONArray())

        val palette = JSONArray()
            .put(JSONArray().put(0).put(0).put(0))
            .put(JSONArray().put(255).put(255).put(255))

        return JSONObject()
            .put("type", "dpaint")
            .put("version", "1")
            .put("image", image)
            .put("palette", palette)
            .put("paletteList", JSONArray().put(palette))
            .put("paletteIndex", 0)
            .put("errorCount", 0)
    }

    private fun bitmapToDataUrl(bitmap: Bitmap): String {
        val out = ByteArrayOutputStream()
        bitmap.compress(Bitmap.CompressFormat.PNG, 100, out)
        val b64 = Base64.encodeToString(out.toByteArray(), Base64.NO_WRAP)
        return "data:image/png;base64,$b64"
    }

    private fun decodeDataUrlBitmap(dataUrl: String): Bitmap? {
        val marker = "base64,"
        val start = dataUrl.indexOf(marker)
        val payload = if (start >= 0) dataUrl.substring(start + marker.length) else dataUrl
        return runCatching {
            val bytes = Base64.decode(payload, Base64.DEFAULT)
            BitmapFactory.decodeByteArray(bytes, 0, bytes.size)
        }.getOrNull()
    }

    private fun readUriText(uri: Uri): String? =
        runCatching {
            contentResolver.openInputStream(uri)?.bufferedReader(Charsets.UTF_8)?.use { it.readText() }
        }.getOrNull()

    private fun documentDisplayName(uri: Uri): String? =
        runCatching {
            contentResolver.query(uri, arrayOf(OpenableColumns.DISPLAY_NAME), null, null, null)?.use { cursor ->
                if (!cursor.moveToFirst()) return@use null
                val idx = cursor.getColumnIndex(OpenableColumns.DISPLAY_NAME)
                if (idx < 0) return@use null
                cursor.getString(idx)
            }
        }.getOrNull()

    private fun normalizeDocumentBaseName(displayName: String?): String {
        val cleaned = displayName
            ?.substringBeforeLast('.', displayName)
            ?.trim()
            ?.replace(Regex("""[\\/:*?"<>|]"""), "_")
            ?.ifBlank { null }
        return cleaned ?: defaultDocumentBaseName()
    }

    /** Default document base name: BooxDraw_ prefix plus the current ISO date (YYYY-MM-DD). */
    private fun defaultDocumentBaseName(): String = "BooxDraw_${LocalDate.now()}"

    private fun buildOpenDocumentIntent(): Intent {
        val intent = Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
            addCategory(Intent.CATEGORY_OPENABLE)
            type = "*/*"
            putExtra(Intent.EXTRA_MIME_TYPES, openMimeTypes)
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        }
        val initialUri = lastOpenUri()
        if (initialUri != null && Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            intent.putExtra(DocumentsContract.EXTRA_INITIAL_URI, initialUri)
        }
        return intent
    }

    private fun prefs() = getSharedPreferences(PREFS_NAME, MODE_PRIVATE)

    /** Restore brush style, per-brush widths, ink color and picker color into the in-memory fields. */
    private fun loadToolbarPrefs() {
        val p = prefs()
        val styleName = p.getString(KEY_BRUSH_STYLE, null)
        selectedBrushStyle = HardwarePenStyle.entries.firstOrNull { it.name == styleName }
            ?: HardwarePenStyle.PENCIL
        runCatching {
            val widths = JSONObject(p.getString(KEY_BRUSH_WIDTHS, "{}") ?: "{}")
            HardwarePenStyle.entries.forEach { style ->
                if (widths.has(style.name)) {
                    brushWidths[style] = widths.getDouble(style.name).toFloat()
                }
            }
        }
        eraserWidthPx = p.getFloat(KEY_ERASER_WIDTH, 30f)
        currentInkColor = p.getInt(KEY_INK_COLOR, Color.BLACK)
        pickerDotColor = p.getInt(KEY_PICKER_COLOR, Color.BLUE)
        viewportLocked = p.getBoolean(KEY_VIEWPORT_LOCKED, false)
        recentColors.clear()
        runCatching {
            val history = JSONArray(p.getString(KEY_COLOR_HISTORY, "[]") ?: "[]")
            for (i in 0 until history.length()) recentColors.addLast(history.getInt(i))
        }
    }

    /** Reflect the current viewport-lock state in the menu item label. */
    private fun updateLockViewportLabel(label: TextView) {
        label.text = if (viewportLocked) "\u2713 Lock view" else "Lock view"
    }

    /** Persist the current toolbar settings. Called from onPause. */
    private fun saveToolbarPrefs() {
        val widths = JSONObject()
        brushWidths.forEach { (style, width) -> widths.put(style.name, width.toDouble()) }
        val history = JSONArray()
        recentColors.forEach { history.put(it) }
        prefs().edit()
            .putString(KEY_BRUSH_STYLE, selectedBrushStyle.name)
            .putString(KEY_BRUSH_WIDTHS, widths.toString())
            .putFloat(KEY_ERASER_WIDTH, eraserWidthPx)
            .putInt(KEY_INK_COLOR, currentInkColor)
            .putInt(KEY_PICKER_COLOR, pickerDotColor)
            .putBoolean(KEY_VIEWPORT_LOCKED, viewportLocked)
            .putString(KEY_COLOR_HISTORY, history.toString())
            .apply()
    }

    private fun autosaveFile(): File = File(filesDir, AUTOSAVE_FILE_NAME)

    /** Serialize the current document to internal storage. Called from onPause. */
    private fun saveAutosaveCanvas() {
        val snapshot = penView.snapshotDocumentForExport() ?: return
        runCatching {
            val json = buildDpaintJson(snapshot, currentDocumentBaseName)
            autosaveFile().writeText(json.toString(), Charsets.UTF_8)
        }
        snapshot.layers.forEach { if (!it.bitmap.isRecycled) it.bitmap.recycle() }
    }

    /**
     * Restore the autosaved document once the pen surface has a valid size. Skipped when an
     * incoming VIEW intent is pending so it does not clobber a file the user asked to open.
     */
    private fun restoreAutosaveWhenReady() {
        if (pendingIncomingViewUri != null) return
        val file = autosaveFile()
        if (!file.exists()) return
        if (penView.width <= 0 || penView.height <= 0) {
            penView.postDelayed({ restoreAutosaveWhenReady() }, 32L)
            return
        }
        val text = runCatching { file.readText(Charsets.UTF_8) }.getOrNull() ?: return
        loadDpaintFromText(text)
    }

    private fun rememberLastOpenUri(uri: Uri) {
        prefs().edit().putString(KEY_LAST_OPEN_URI, uri.toString()).apply()
    }

    private fun lastOpenUri(): Uri? {
        val raw = prefs().getString(KEY_LAST_OPEN_URI, null) ?: return null
        return runCatching { Uri.parse(raw) }.getOrNull()
    }

    private fun beginUiTouch() {
        uiTouchDepth += 1
        updateRawSuppression()
    }

    private fun endUiTouch(reset: Boolean) {
        uiTouchDepth = if (reset) 0 else (uiTouchDepth - 1).coerceAtLeast(0)
        updateRawSuppression()
    }

    private fun guardRawMode(view: View) {
        view.setOnTouchListener { _, event ->
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN, MotionEvent.ACTION_POINTER_DOWN -> beginUiTouch()
                MotionEvent.ACTION_UP, MotionEvent.ACTION_POINTER_UP -> endUiTouch(false)
                MotionEvent.ACTION_CANCEL -> endUiTouch(true)
            }
            false
        }
    }

    private fun bindImmediateDownAction(view: View, onDown: () -> Unit) {
        view.setOnTouchListener { v, event ->
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    beginUiTouch()
                    v.isPressed = true
                    onDown()
                    true
                }

                MotionEvent.ACTION_UP -> {
                    v.isPressed = false
                    endUiTouch(false)
                    v.performClick()
                    true
                }

                MotionEvent.ACTION_CANCEL -> {
                    v.isPressed = false
                    endUiTouch(true)
                    true
                }

                else -> true
            }
        }
    }

    private fun updateRawSuppression() {
        val suppress = activityPaused ||
            pickerInFlight ||
            aboutDialogVisible ||
            eraserUiTransitionInFlight ||
            historyUiTransitionInFlight ||
            overlayDismissInFlight ||
            uiTouchDepth > 0 ||
            layerPanel.visibility == View.VISIBLE ||
            colorPickerPanel.visibility == View.VISIBLE ||
            fileMenuPanel.visibility == View.VISIBLE
        penView.setRawInputSuppressed(suppress)
    }

    private fun showAboutDialog() {
        aboutDialogVisible = true
        updateRawSuppression()

        val content = layoutInflater.inflate(R.layout.dialog_about, null)
        val imageView = content.findViewById<android.widget.ImageView>(R.id.aboutImage)
        val textColumn = content.findViewById<LinearLayout>(R.id.aboutTextColumn)
        val linkView = content.findViewById<TextView>(R.id.aboutLink)
        val okButton = content.findViewById<TextView>(R.id.aboutOkButton)
        val linkText = SpannableStringBuilder("Open source - fork me on Github").apply {
            val start = lastIndexOf("Github")
            if (start >= 0) {
                val end = start + "Github".length
                setSpan(
                    URLSpan("https://github.com/steffest/Boox-EinkDraw"),
                    start,
                    end,
                    Spanned.SPAN_EXCLUSIVE_EXCLUSIVE
                )
            }
        }
        linkView.text = linkText
        linkView.movementMethod = LinkMovementMethod.getInstance()

        val dialog = Dialog(this, R.style.Theme_BooxEinkDraw_AboutDialog).apply {
            setContentView(content)
            setCancelable(true)
            setCanceledOnTouchOutside(true)
            window?.setBackgroundDrawable(ColorDrawable(Color.TRANSPARENT))
        }

        okButton.setOnClickListener { dialog.dismiss() }
        dialog.setOnDismissListener {
            aboutDialogVisible = false
            updateRawSuppression()
        }
        dialog.show()
        content.post {
            val side = textColumn.height.coerceAtLeast(dp(96))
            val lp = imageView.layoutParams
            if (lp.width != side || lp.height != side) {
                lp.width = side
                lp.height = side
                imageView.layoutParams = lp
            }
            dialog.window?.setLayout(
                android.view.ViewGroup.LayoutParams.WRAP_CONTENT,
                android.view.ViewGroup.LayoutParams.WRAP_CONTENT
            )
        }
    }

    override fun dispatchTouchEvent(ev: MotionEvent): Boolean {
        when (ev.actionMasked) {
            MotionEvent.ACTION_DOWN -> {
                if (dismissPanelsIfTappedOutside(ev.rawX, ev.rawY)) {
                    // Swallow the whole gesture so the tap-to-close does not draw a stroke.
                    consumingDismissGesture = true
                    return true
                }
            }
            MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                if (consumingDismissGesture) {
                    consumingDismissGesture = false
                    return true
                }
            }
            else -> {
                if (consumingDismissGesture) return true
            }
        }
        return super.dispatchTouchEvent(ev)
    }

    override fun dispatchKeyEvent(event: KeyEvent): Boolean {
        val isStylusKey = when (event.keyCode) {
            KeyEvent.KEYCODE_STYLUS_BUTTON_PRIMARY,
            KeyEvent.KEYCODE_STYLUS_BUTTON_SECONDARY,
            KeyEvent.KEYCODE_STYLUS_BUTTON_TERTIARY,
            -> true
            else -> false
        }
        if (isStylusKey) {
            val action = when (event.action) {
                KeyEvent.ACTION_DOWN -> "DOWN"
                KeyEvent.ACTION_UP -> "UP"
                else -> "ACTION_${event.action}"
            }
            Log.i(
                TAG,
                "stylusKey action=$action key=${KeyEvent.keyCodeToString(event.keyCode)} " +
                    "repeat=${event.repeatCount} source=0x${event.source.toString(16)} device=${event.device?.name}"
            )
        }
        return super.dispatchKeyEvent(event)
    }

    private fun dismissPanelsIfTappedOutside(rawX: Float, rawY: Float): Boolean {
        var dismissed = false

        if (layerPanel.visibility == View.VISIBLE &&
            !isPointInsideView(layerPanel, rawX, rawY) &&
            !isPointInsideView(buttonLayers, rawX, rawY)
        ) {
            layerPanel.visibility = View.GONE
            dismissed = true
        }

        if (fileMenuPanel.visibility == View.VISIBLE &&
            !isPointInsideView(fileMenuPanel, rawX, rawY) &&
            !isPointInsideView(buttonMenu, rawX, rawY)
        ) {
            fileMenuPanel.visibility = View.GONE
            dismissed = true
        }

        if (colorPickerPanel.visibility == View.VISIBLE &&
            !isPointInsideView(colorPickerPanel, rawX, rawY) &&
            !isPointInsideView(swatchBlue, rawX, rawY)
        ) {
            colorPickerPanel.visibility = View.GONE
            onColorPickerPanelClosed()
            dismissed = true
        }

        if (dismissed) {
            // Set the dismiss flag before updating suppression so raw drawing is never re-enabled
            // mid-gesture; otherwise the still-down pen starts a stroke via the Onyx path.
            overlayDismissInFlight = true
            refreshPickerToggleSwatch(active = colorPickerPanel.visibility == View.VISIBLE)
            updateRawSuppression()
            refreshUiAfterOverlayDismiss()
        }
        return dismissed
    }

    private fun refreshUiAfterOverlayDismiss() {
        rootFrame.invalidate()
        penView.invalidate()
        // Raw drawing stays suppressed via overlayDismissInFlight (set by the caller) and the view
        // redraw pass has not run yet. Wait for the redraw, force a full e-ink refresh to clear the
        // pixels where the panel was, then re-enable raw drawing.
        val decor = window?.decorView ?: rootFrame
        rootFrame.postDelayed({
            runCatching {
                // GC does a full refresh with a flash to clear ghosting from where the panel was;
                // GU leaves residual ghosting on large filled areas like a dismissed panel.
                EpdController.invalidate(decor, UpdateMode.GC)
                EpdController.refreshScreen(decor, UpdateMode.GC)
            }
        }, 80L)
        pendingOverlayDismissReset?.let { rootFrame.removeCallbacks(it) }
        val reset = Runnable {
            overlayDismissInFlight = false
            updateRawSuppression()
        }
        pendingOverlayDismissReset = reset
        rootFrame.postDelayed(reset, 250L)
    }

    private fun isPointInsideView(view: View, rawX: Float, rawY: Float): Boolean {
        val r = Rect()
        view.getGlobalVisibleRect(r)
        return r.contains(rawX.roundToInt(), rawY.roundToInt())
    }

    override fun onPause() {
        super.onPause()
        activityPaused = true
        saveToolbarPrefs()
        saveAutosaveCanvas()
        updateRawSuppression()
    }

    override fun onResume() {
        super.onResume()
        activityPaused = false
        updateRawSuppression()
    }

    private fun dp(v: Int): Int = (v * resources.displayMetrics.density).roundToInt()

    private fun dpF(v: Float): Float = v * resources.displayMetrics.density
}
