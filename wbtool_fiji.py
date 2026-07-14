from ij import IJ, ImagePlus, Prefs
from ij.gui import GenericDialog, Overlay, Line, TextRoi
from ij.process import ImageConverter
import java.awt as awt
from java.awt import (Color, Font, BasicStroke, RenderingHints,
                      BorderLayout, Dimension)
from java.awt.geom import GeneralPath, AffineTransform
from java.awt.event import ActionListener, MouseAdapter, MouseEvent, KeyEvent, WindowAdapter
from javax.swing import (JFrame, JPanel, JButton, JLabel, JSeparator,
                         JScrollPane, JList, DefaultListModel,
                         ListSelectionModel, BorderFactory,
                         JOptionPane, BoxLayout, Box, JFileChooser,
                         KeyStroke, AbstractAction, JTextArea)
from javax.swing.filechooser import FileNameExtensionFilter
from com.itextpdf.text import Document as PdfDocument
from com.itextpdf.text.pdf import PdfWriter
import math
from java.io import FileOutputStream
from java.awt.image import BufferedImage
from javax.imageio import ImageIO
import java.io.File as JFile
TICK_LEN     = 20
TICK_GAP     = 4
LEFT_MARGIN  = 90
BAND_GAP     = 30
TOP_MARGIN   = 60
LABEL_PAD    = 8
FIG_INIT_W   = 800
FONT_KDA     = Font("Arial", Font.PLAIN, 11)
FONT_NAME    = Font("Arial", Font.BOLD,  12)
FONT_SAMPLE  = Font("Arial", Font.PLAIN, 11)
FONT_ANNOT   = Font("Arial", Font.PLAIN, 11)
FONT_BANDANN = Font("Arial", Font.PLAIN, 11)
COLOR_ACTIVE   = Color(255, 180, 0)
COLOR_INACTIVE = None
HIT_RADIUS   = 8
HANDLE_SIZE  = 7
PASTE_OFFSET = 12
SL_HIT_R     = 12    # hit radius for sample label anchor point
BA_HIT_R     = 8     # hit radius for right-side band annotation markers
TRI_DEFAULT_H = 28
TRI_FILL     = Color.BLACK
def sized_font(base_font, size):
    return Font(base_font.getName(), base_font.getStyle(),
                int(max(5, min(72, round(size)))))
def rich_text_runs(text):
    runs = []
    i = 0
    plain = ""
    while i < len(text):
        if i + 1 < len(text) and text[i] in ("^", "_") and text[i + 1] == "{":
            if plain:
                runs.append(("normal", plain))
                plain = ""
            kind = "sup" if text[i] == "^" else "sub"
            j = i + 2
            part = ""
            while j < len(text) and text[j] != "}":
                part += text[j]
                j += 1
            if j < len(text) and text[j] == "}":
                runs.append((kind, part))
                i = j + 1
            else:
                plain += text[i]
                i += 1
        else:
            plain += text[i]
            i += 1
    if plain:
        runs.append(("normal", plain))
    return runs
def plain_text(text):
    return "".join(part for kind, part in rich_text_runs(text))
def rich_text_lines(text):
    return (text or "").split("\n")
def rich_text_line_width(g, base_font, text):
    width = 0
    base_size = base_font.getSize()
    for kind, part in rich_text_runs(text):
        f = base_font if kind == "normal" else sized_font(base_font, base_size * 0.70)
        width += g.getFontMetrics(f).stringWidth(part)
    return width
def rich_text_width(g, base_font, text):
    width = 0
    for line in rich_text_lines(text):
        width = max(width, rich_text_line_width(g, base_font, line))
    return width
def draw_rich_text(g, text, base_font, x, baseline_y):
    lines = rich_text_lines(text)
    if len(lines) > 1:
        line_h = g.getFontMetrics(base_font).getHeight()
        for i, line in enumerate(lines):
            draw_rich_text(g, line, base_font, x, baseline_y + i * line_h)
        return
    cx = float(x)
    base_size = base_font.getSize()
    for kind, part in rich_text_runs(text):
        if kind == "normal":
            f = base_font
            y = baseline_y
        else:
            f = sized_font(base_font, base_size * 0.70)
            shift = base_size * 0.38
            y = baseline_y - shift if kind == "sup" else baseline_y + shift * 0.55
        g.setFont(f)
        g.drawString(part, int(round(cx)), int(round(y)))
        cx += g.getFontMetrics(f).stringWidth(part)
def draw_rich_text_block(g, text, base_font, x, baseline_y):
    fm = g.getFontMetrics(base_font)
    line_h = fm.getHeight()
    for i, line in enumerate(rich_text_lines(text)):
        draw_rich_text(g, line, base_font, x, baseline_y + i * line_h)
def rich_text_block_rect(g, base_font, x, baseline_y, text):
    fm = g.getFontMetrics(base_font)
    lines = rich_text_lines(text)
    width = rich_text_width(g, base_font, text)
    height = fm.getHeight() * max(1, len(lines))
    return (x - 2, baseline_y - fm.getAscent() - 2, width + 4, height + 4)
def ask_string(title, prompt, default=""):
    panel = JPanel()
    panel.setLayout(BoxLayout(panel, BoxLayout.Y_AXIS))
    panel.add(JLabel(prompt))
    field = JTextArea(default, 4, 24)
    field.setLineWrap(True)
    field.setWrapStyleWord(True)
    panel.add(JScrollPane(field))
    btn_row = JPanel()
    btn_row.setLayout(BoxLayout(btn_row, BoxLayout.X_AXIS))
    def insert_markup(mark):
        start = field.getSelectionStart()
        end = field.getSelectionEnd()
        selected = field.getSelectedText()
        if selected is None:
            selected = ""
        insert = mark + "{" + selected + "}"
        field.replaceSelection(insert)
        if selected:
            field.select(start + 2, start + 2 + len(selected))
        else:
            field.setCaretPosition(start + 2)
        field.requestFocusInWindow()
    class _ScriptAction(ActionListener):
        def __init__(self, mark):
            self.mark = mark
        def actionPerformed(self, event):
            insert_markup(self.mark)
    sup = JButton(u"\u25a1\u02e3")
    sub = JButton(u"\u25a1\u2093")
    sup.setToolTipText("Superscript selected text")
    sub.setToolTipText("Subscript selected text")
    sup.addActionListener(_ScriptAction("^"))
    sub.addActionListener(_ScriptAction("_"))
    btn_row.add(sup)
    btn_row.add(Box.createHorizontalStrut(4))
    btn_row.add(sub)
    panel.add(Box.createVerticalStrut(4))
    panel.add(btn_row)
    pane = JOptionPane(panel, JOptionPane.PLAIN_MESSAGE,
                       JOptionPane.OK_CANCEL_OPTION)
    pane.setInitialValue(field)
    dialog = pane.createDialog(None, title)
    enter = KeyStroke.getKeyStroke(KeyEvent.VK_ENTER, 0)
    shift_enter = KeyStroke.getKeyStroke(KeyEvent.VK_ENTER,
                                         awt.event.InputEvent.SHIFT_DOWN_MASK)
    class _AcceptAction(AbstractAction):
        def actionPerformed(self, event):
            pane.setValue(JOptionPane.OK_OPTION)
            dialog.dispose()
    field.getInputMap().put(enter, "accept-dialog")
    field.getActionMap().put("accept-dialog", _AcceptAction())
    field.getInputMap().put(shift_enter, "insert-break")
    class _FocusAction(WindowAdapter):
        def _focus(self):
            field.selectAll()
            field.requestFocus()
            field.grabFocus()
            field.requestFocusInWindow()
            field.selectAll()
        def windowOpened(self, event):
            self._focus()
        def windowGainedFocus(self, event):
            self._focus()
    fa = _FocusAction()
    dialog.addWindowListener(fa)
    dialog.addWindowFocusListener(fa)
    dialog.setAlwaysOnTop(True)
    dialog.toFront()
    dialog.setVisible(True)
    result = pane.getValue()
    if result != JOptionPane.OK_OPTION:
        return None
    return field.getText().strip()
def ask_float(title, prompt, default=0.0):
    gd = GenericDialog(title)
    gd.addNumericField(prompt, default, 1)
    gd.setAlwaysOnTop(True)
    gd.toFront()
    gd.showDialog()
    if gd.wasCanceled():
        return None
    return gd.getNextNumber()
def ask_int(title, prompt, default=300):
    gd = GenericDialog(title)
    gd.addNumericField(prompt, default, 0)
    gd.showDialog()
    if gd.wasCanceled():
        return None
    return int(gd.getNextNumber())
def kda_label_text(value):
    return str(value).strip()
def crop_imp(imp, x, y, w, h):
    imp.setRoi(x, y, w, h)
    cropped = imp.crop()
    imp.killRoi()
    return cropped
def open_rgb_image(parent, last_dir):
    fc = JFileChooser()
    fc.setFileFilter(FileNameExtensionFilter(
        "Image files", ["tif","tiff","png","jpg","jpeg"]))
    if last_dir is not None:
        fc.setCurrentDirectory(JFile(last_dir))
    if fc.showOpenDialog(parent) != JFileChooser.APPROVE_OPTION:
        return None, last_dir
    chosen = fc.getSelectedFile()
    new_last_dir = chosen.getParent()
    Prefs.set("wbtool.last_dir", new_last_dir)
    path = chosen.getAbsolutePath()
    imp = IJ.openImage(path)
    if imp is None:
        JOptionPane.showMessageDialog(parent,
            "Could not open: " + path, "Error",
            JOptionPane.ERROR_MESSAGE)
        return None, new_last_dir
    if imp.getType() != ImagePlus.COLOR_RGB:
        ImageConverter(imp).convertToRGB()
    return imp, new_last_dir
def show_image_right_half(imp):
    imp.show()
    screen = awt.Toolkit.getDefaultToolkit().getScreenSize()
    win = imp.getWindow()
    if win is not None:
        win.setLocation(screen.width // 2, 0)
        win.setSize(screen.width // 2, screen.height)
def set_crop_selection_tool():
    try:
        IJ.setTool("rotated rectangle")
    except:
        IJ.setTool("rectangle")
def rotated_crop_from_roi(imp, roi):
    bounds = roi.getBounds()
    x, y, w, h = bounds.x, bounds.y, bounds.width, bounds.height
    angle = 0.0
    try:
        fp = roi.getFloatPolygon()
    except:
        fp = None
    if fp is not None and fp.npoints >= 4:
        xs = [fp.xpoints[i] for i in range(fp.npoints)]
        ys = [fp.ypoints[i] for i in range(fp.npoints)]
        p0 = (float(xs[0]), float(ys[0]))
        p1 = (float(xs[1]), float(ys[1]))
        p2 = (float(xs[2]), float(ys[2]))
        side_w = dist2(p0[0], p0[1], p1[0], p1[1])
        side_h = dist2(p1[0], p1[1], p2[0], p2[1])
        if side_w >= 2 and side_h >= 2:
            x = p0[0]; y = p0[1]
            w = int(round(side_w)); h = int(round(side_h))
            angle = math.atan2(p1[1] - p0[1], p1[0] - p0[0])
    if w < 2 or h < 2:
        return None
    if abs(angle) < 0.0001:
        cropped = crop_imp(imp, int(round(x)), int(round(y)), int(round(w)), int(round(h)))
        return cropped, float(x), float(y), int(round(w)), int(round(h)), 0.0
    src_bi = imp.getProcessor().convertToRGB().getBufferedImage()
    out = BufferedImage(int(round(w)), int(round(h)), BufferedImage.TYPE_INT_RGB)
    g = out.createGraphics()
    g.setRenderingHint(RenderingHints.KEY_INTERPOLATION,
                       RenderingHints.VALUE_INTERPOLATION_BICUBIC)
    g.setColor(Color.WHITE)
    g.fillRect(0, 0, out.getWidth(), out.getHeight())
    c = math.cos(angle); s = math.sin(angle)
    tx = -(c * x + s * y)
    ty = (s * x - c * y)
    at = AffineTransform(c, -s, s, c, tx, ty)
    g.drawImage(src_bi, at, None)
    g.dispose()
    return ImagePlus("Rotated crop", out), float(x), float(y), out.getWidth(), out.getHeight(), math.degrees(angle)
def marker_y_in_crop(marker, crop_x, crop_y, crop_angle_deg):
    px = float(marker.get("x_abs", 0.0))
    py = float(marker.get("y_abs", marker.get("y_orig", 0.0)))
    a = math.radians(crop_angle_deg)
    dx = px - crop_x
    dy = py - crop_y
    return -math.sin(a) * dx + math.cos(a) * dy
def dist2(ax, ay, bx, by):
    return math.sqrt((ax - bx) ** 2 + (ay - by) ** 2)
def sl_anchor(sl, ix, iy, dw):
    """Return the scene (x, y) anchor point of a sample label."""
    cx = ix + int(round(sl["x_frac"] * dw))
    cy = iy - LABEL_PAD
    return float(cx), float(cy)
class Band(object):
    def __init__(self, crop_imp, kda_markers, protein_name, width=None):
        self.orig_imp     = crop_imp
        self.orig_w       = crop_imp.getWidth()
        self.orig_h       = crop_imp.getHeight()
        self.kda_markers  = kda_markers
        self.protein_name = protein_name
        self.display_w    = width if width else self.orig_w
        self.sample_labels = []
        self.band_annots   = []
        self.protein_size  = FONT_NAME.getSize()
        self.protein_dx_frac = 0.0
        self.protein_dy_frac = 0.0
        self.x_offset = 0.0
        self.y_offset = 0.0
        self.crop_x=None; self.crop_y=None; self.crop_w=None; self.crop_h=None
        self.crop_angle=0.0
    def scale(self):
        return float(self.display_w) / float(self.orig_w)
    def display_h(self):
        return int(round(self.orig_h * self.scale()))
class HLine(object):
    def __init__(self, x0, y, x1, band_ref=None,
                 x0_frac=None, x1_frac=None, y_frac=None):
        self.x0 = float(x0)
        self.y  = float(y)
        self.x1 = float(x1)
        self.band_ref = band_ref
        self.x0_frac  = x0_frac
        self.x1_frac  = x1_frac
        self.y_frac   = y_frac
    def shallow_copy(self):
        return HLine(self.x0, self.y, self.x1, self.band_ref,
                     self.x0_frac, self.x1_frac, self.y_frac)
class TriangleAnnot(object):
    def __init__(self, x0, y, x1, height=TRI_DEFAULT_H, band_ref=None,
                 x0_frac=None, x1_frac=None, y_frac=None, h_frac=None):
        self.x0 = float(x0)
        self.y = float(y)
        self.x1 = float(x1)
        self.height = float(max(4.0, height))
        self.band_ref = band_ref
        self.x0_frac = x0_frac
        self.x1_frac = x1_frac
        self.y_frac = y_frac
        self.h_frac = h_frac
    def points(self):
        return [(self.x0, self.y),
                (self.x0, self.y + self.height),
                (self.x1, self.y + self.height)]
    def shallow_copy(self):
        return TriangleAnnot(self.x0, self.y, self.x1, self.height,
                             self.band_ref, self.x0_frac, self.x1_frac,
                             self.y_frac, self.h_frac)
class FreeText(object):
    def __init__(self, x, y, text):
        self.x    = float(x)
        self.y    = float(y)
        self.text = text
        self.font_size = FONT_ANNOT.getSize()
    def shallow_copy(self):
        ft = FreeText(self.x, self.y, self.text)
        ft.font_size = self.font_size
        return ft
class FigureRenderer(object):
    def band_extra_bottom(self, b):
        dh = b.display_h()
        size = getattr(b, "protein_size", FONT_NAME.getSize())
        dy = getattr(b, "protein_dy_frac", 0.0) * dh
        line_count = max(1, len(rich_text_lines(b.protein_name)))
        if b.band_annots:
            baseline_y = dh + size + 5 + dy
        else:
            baseline_y = dh / 2.0 + size / 2.0 + dy
        text_bottom = baseline_y + (line_count - 1) * size * 1.25 + size * 0.30
        return max(0, int(math.ceil(text_bottom - dh)) + 6)
    def band_step(self, b):
        return b.display_h() + BAND_GAP + self.band_extra_bottom(b)
    def band_img_rect(self, band_idx, bands):
        y_cursor = TOP_MARGIN
        for i, b in enumerate(bands):
            dh = b.display_h()
            if i == band_idx:
                ix = LEFT_MARGIN + int(round(getattr(b, "x_offset", 0.0)))
                iy = y_cursor + int(round(getattr(b, "y_offset", 0.0)))
                return (ix, iy, b.display_w, dh)
            y_cursor += self.band_step(b)
        return None
    def recompute_hline(self, hl, bands):
        if hl.band_ref is None or hl.band_ref not in bands:
            hl.band_ref = None
            return
        idx  = bands.index(hl.band_ref)
        rect = self.band_img_rect(idx, bands)
        if rect is None:
            return
        img_x, img_y, dw, dh = rect
        hl.x0 = img_x + hl.x0_frac * dw
        hl.x1 = img_x + hl.x1_frac * dw
        hl.y  = img_y + hl.y_frac  * dh
    def recompute_triangle(self, tri, bands):
        if tri.band_ref is None or tri.band_ref not in bands:
            tri.band_ref = None
            return
        if (tri.x0_frac is None or tri.x1_frac is None
                or tri.y_frac is None or tri.h_frac is None):
            return
        idx = bands.index(tri.band_ref)
        rect = self.band_img_rect(idx, bands)
        if rect is None:
            return
        img_x, img_y, dw, dh = rect
        tri.x0 = img_x + tri.x0_frac * dw
        tri.x1 = img_x + tri.x1_frac * dw
        tri.y = img_y + tri.y_frac * dh
        tri.height = max(4.0, tri.h_frac * dh)
    def canvas_height(self, bands, hlines, triangles, freetexts):
        if not bands and not hlines and not triangles and not freetexts:
            return 300
        total_h = TOP_MARGIN
        for i, b in enumerate(bands):
            rect = self.band_img_rect(i, bands)
            if rect is not None:
                ix, iy, dw, dh = rect
                total_h = max(total_h, iy + dh + self.band_extra_bottom(b) + BAND_GAP)
        return max(total_h, 300)
    def draw(self, g, bands, hlines, triangles, freetexts, canvas_w,
             selected=None, edit_mode=False):
        for hl in hlines:
            self.recompute_hline(hl, bands)
        for tri in triangles:
            self.recompute_triangle(tri, bands)
        total_h = self.canvas_height(bands, hlines, triangles, freetexts)
        g.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
                           RenderingHints.VALUE_ANTIALIAS_ON)
        g.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING,
                           RenderingHints.VALUE_TEXT_ANTIALIAS_ON)
        g.setColor(Color.WHITE);  g.fillRect(0, 0, canvas_w, total_h)
        if not bands and not hlines and not triangles and not freetexts:
            g.setColor(Color.LIGHT_GRAY)
            g.setFont(Font("Arial", Font.ITALIC, 14))
            g.drawString("No bands yet — crop from the gel image", 40, 150)
            return
        y_cursor = TOP_MARGIN
        for idx, b in enumerate(bands):
            sc    = b.scale()
            dw    = b.display_w
            dh    = b.display_h()
            ix, iy, dw, dh = self.band_img_rect(idx, bands)
            src_bi = b.orig_imp.getProcessor().convertToRGB().getBufferedImage()
            g.drawImage(src_bi, ix, iy, dw, dh, None)
            g.setColor(Color.BLACK)
            g.setStroke(BasicStroke(1.5))
            g.drawRect(ix, iy, dw, dh)
            for m in b.kda_markers:
                ty = iy + int(round(m["y_orig"] * sc))
                x1 = ix - 2;  x0 = x1 - TICK_LEN
                kda_font = sized_font(FONT_KDA, m.get("font_size", FONT_KDA.getSize()))
                g.setFont(kda_font)
                fm = g.getFontMetrics()
                is_sel = (edit_mode and isinstance(selected, tuple)
                          and selected[0] == "kda"
                          and selected[1] is b
                          and selected[2] is m)
                g.setColor(Color.BLACK)
                g.setStroke(BasicStroke(1.2))
                g.drawLine(x0, ty, x1, ty)
                lbl = kda_label_text(m["kda"])
                lw  = fm.stringWidth(lbl)
                if is_sel:
                    g.setColor(Color(0, 100, 220))
                kda_base_y = ty + (fm.getAscent() - fm.getDescent()) // 2
                g.drawString(lbl, x0 - TICK_GAP - lw, kda_base_y)
                if is_sel:
                    th = fm.getHeight()
                    g.setStroke(BasicStroke(1.0,
                        BasicStroke.CAP_BUTT, BasicStroke.JOIN_BEVEL,
                        0, [3, 3], 0))
                    g.drawRect(x0 - TICK_GAP - lw - 2, ty - th // 2 - 2,
                               lw + 4, th + 4)
                    g.setStroke(BasicStroke(1.0))
            for ba in b.band_annots:
                ty = iy + int(round(ba["y_frac"] * dh))
                x0 = ix + dw + 2;  x1 = x0 + TICK_LEN
                ba_font = sized_font(FONT_BANDANN,
                                     ba.get("font_size", FONT_BANDANN.getSize()))
                g.setFont(ba_font)
                fm_ba = g.getFontMetrics()
                is_sel = (edit_mode and isinstance(selected, tuple)
                          and selected[0] == "ba"
                          and selected[1] is b
                          and selected[2] is ba)
                g.setColor(Color(0, 100, 220) if is_sel else Color.BLACK)
                g.setStroke(BasicStroke(1.2))
                g.drawLine(x0, ty, x1, ty)
                ba_base_y = ty + (fm_ba.getAscent() - fm_ba.getDescent()) // 2
                draw_rich_text(g, ba["text"], ba_font, x1 + TICK_GAP,
                               ba_base_y)
                if is_sel:
                    tw = rich_text_width(g, ba_font, ba["text"])
                    th = fm_ba.getHeight()
                    g.setStroke(BasicStroke(1.0,
                        BasicStroke.CAP_BUTT, BasicStroke.JOIN_BEVEL,
                        0, [3, 3], 0))
                    g.drawRect(x1 + TICK_GAP - 2, ty - th // 2 - 2,
                               tw + 4, th + 4)
                    g.setStroke(BasicStroke(1.0))
            name_font = sized_font(FONT_NAME, getattr(b, "protein_size",
                                                      FONT_NAME.getSize()))
            g.setFont(name_font)
            fm2 = g.getFontMetrics()
            name_sel = (edit_mode and isinstance(selected, tuple)
                        and selected[0] == "protein"
                        and selected[1] is b)
            g.setColor(Color(0, 100, 220) if name_sel else Color.BLACK)
            if b.band_annots:
                name_w = rich_text_width(g, name_font, b.protein_name)
                name_x = ix + dw // 2 - name_w // 2
                name_y = iy + dh + fm2.getAscent() + 5
            else:
                name_w = rich_text_width(g, name_font, b.protein_name)
                name_x = ix + dw + 10
                name_y = iy + dh // 2 + fm2.getAscent() // 2
            name_x += int(round(getattr(b, "protein_dx_frac", 0.0) * dw))
            name_y += int(round(getattr(b, "protein_dy_frac", 0.0) * dh))
            draw_rich_text(g, b.protein_name, name_font, name_x, name_y)
            if name_sel:
                th = fm2.getHeight() * max(1, len(rich_text_lines(b.protein_name)))
                g.setStroke(BasicStroke(1.0,
                    BasicStroke.CAP_BUTT, BasicStroke.JOIN_BEVEL,
                    0, [3, 3], 0))
                g.drawRect(name_x - 2, name_y - fm2.getAscent() - 2,
                           name_w + 4, th + 4)
                g.setStroke(BasicStroke(1.0))
            for sl in b.sample_labels:
                ax, ay = sl_anchor(sl, ix, iy, dw)
                sl_font = sized_font(FONT_SAMPLE,
                                     sl.get("font_size", FONT_SAMPLE.getSize()))
                text_w = rich_text_width(g, sl_font, sl["text"])
                lx = int(ax) - int(text_w / 2.0)
                ly = int(ay)
                is_sel = (edit_mode and isinstance(selected, tuple)
                          and selected[0] == "sl"
                          and selected[1] is b
                          and selected[2] is sl)
                old = g.getTransform()
                g.setColor(Color(0, 100, 220) if is_sel else Color.BLACK)
                g.translate(lx, ly)
                g.rotate(math.radians(-sl["angle"]))
                draw_rich_text(g, sl["text"], sl_font, 0, 0)
                g.setTransform(old)
                if edit_mode:
                    g.setColor(Color(0, 100, 220) if is_sel else Color(130, 185, 245))
                    r = 5 if is_sel else 3
                    g.fillOval(int(ax) - r, int(ay) - r, r*2, r*2)
                    if is_sel:
                        g.setStroke(BasicStroke(1.0))
                        g.drawOval(int(ax) - r - 2, int(ay) - r - 2,
                                   (r + 2)*2, (r + 2)*2)
            y_cursor += self.band_step(b)
        hs = HANDLE_SIZE
        for tri in triangles:
            is_sel = edit_mode and (tri is selected)
            pts = tri.points()
            path = GeneralPath()
            path.moveTo(float(pts[0][0]), float(pts[0][1]))
            for px, py in pts[1:]:
                path.lineTo(float(px), float(py))
            path.closePath()
            g.setColor(Color(0, 100, 220) if is_sel else TRI_FILL)
            g.fill(path)
            if is_sel:
                for px, py in pts:
                    g.fillRect(int(px) - hs//2, int(py) - hs//2, hs, hs)
        hs = HANDLE_SIZE
        for hl in hlines:
            is_sel = edit_mode and (hl is selected)
            g.setColor(Color(0, 100, 220) if is_sel else Color.BLACK)
            g.setStroke(BasicStroke(1.5))
            g.drawLine(int(hl.x0), int(hl.y), int(hl.x1), int(hl.y))
            if is_sel:
                g.fillRect(int(hl.x0) - hs//2, int(hl.y) - hs//2, hs, hs)
                g.fillRect(int(hl.x1) - hs//2, int(hl.y) - hs//2, hs, hs)
        for ft in freetexts:
            is_sel = edit_mode and (ft is selected)
            ft_font = sized_font(FONT_ANNOT, getattr(ft, "font_size",
                                                     FONT_ANNOT.getSize()))
            fm3 = g.getFontMetrics()
            g.setColor(Color(0, 100, 220) if is_sel else Color.BLACK)
            draw_rich_text_block(g, ft.text, ft_font, int(ft.x), int(ft.y))
            if is_sel:
                rx, ry, rw, rh = rich_text_block_rect(g, ft_font, int(ft.x),
                                                      int(ft.y), ft.text)
                g.setStroke(BasicStroke(1.0,
                    BasicStroke.CAP_BUTT, BasicStroke.JOIN_BEVEL,
                    0, [3, 3], 0))
                g.drawRect(int(rx), int(ry), int(rw), int(rh))
                g.setStroke(BasicStroke(1.0))
    def render(self, bands, hlines, triangles, freetexts, canvas_w,
               selected=None, edit_mode=False):
        total_h = self.canvas_height(bands, hlines, triangles, freetexts)
        bi = BufferedImage(canvas_w, total_h, BufferedImage.TYPE_INT_RGB)
        g = bi.createGraphics()
        self.draw(g, bands, hlines, triangles, freetexts, canvas_w,
                  selected, edit_mode)
        g.dispose()
        return bi
class FigureCanvas(JPanel):
    def __init__(self, controller):
        JPanel.__init__(self)
        self.ctrl         = controller
        self.bi           = None
        self.mode         = None
        self._drag_start  = None
        self._drag_last   = None
        self._drag_target = None
        self._drag_band   = None
        self.setFocusable(True)
        canvas = self
        copy_key  = KeyStroke.getKeyStroke(KeyEvent.VK_C, awt.event.InputEvent.CTRL_DOWN_MASK)
        paste_key = KeyStroke.getKeyStroke(KeyEvent.VK_V, awt.event.InputEvent.CTRL_DOWN_MASK)
        undo_key_ctrl = KeyStroke.getKeyStroke(KeyEvent.VK_Z, awt.event.InputEvent.CTRL_DOWN_MASK)
        undo_key_meta = KeyStroke.getKeyStroke(KeyEvent.VK_Z, awt.event.InputEvent.META_DOWN_MASK)
        redo_key_ctrl = KeyStroke.getKeyStroke(KeyEvent.VK_Z, awt.event.InputEvent.CTRL_DOWN_MASK | awt.event.InputEvent.SHIFT_DOWN_MASK)
        redo_key_meta = KeyStroke.getKeyStroke(KeyEvent.VK_Z, awt.event.InputEvent.META_DOWN_MASK | awt.event.InputEvent.SHIFT_DOWN_MASK)
        up_key    = KeyStroke.getKeyStroke(KeyEvent.VK_UP,    0)
        down_key  = KeyStroke.getKeyStroke(KeyEvent.VK_DOWN,  0)
        left_key  = KeyStroke.getKeyStroke(KeyEvent.VK_LEFT,  0)
        right_key = KeyStroke.getKeyStroke(KeyEvent.VK_RIGHT, 0)
        del_key   = KeyStroke.getKeyStroke(KeyEvent.VK_DELETE,     0)
        bsp_key   = KeyStroke.getKeyStroke(KeyEvent.VK_BACK_SPACE, 0)
        class _CopyAction(AbstractAction):
            def actionPerformed(self, e):
                canvas.ctrl.copy_selected()
        class _PasteAction(AbstractAction):
            def actionPerformed(self, e):
                canvas.ctrl.paste_clipboard()
        class _NudgeAction(AbstractAction):
            def __init__(self, axis, delta):
                AbstractAction.__init__(self)
                self.axis  = axis
                self.delta = delta
            def actionPerformed(self, e):
                if canvas.ctrl.edit_mode_active:
                    canvas.ctrl.nudge_annot(self.axis, self.delta)
        class _DeleteAction(AbstractAction):
            def actionPerformed(self, e):
                if canvas.ctrl.edit_mode_active:
                    canvas.ctrl.delete_selected_annot()
        class _UndoAction(AbstractAction):
            def actionPerformed(self, e):
                canvas.ctrl.undo_last_edit()
        class _RedoAction(AbstractAction):
            def actionPerformed(self, e):
                canvas.ctrl.redo_last_undo()
        im = self.getInputMap(JPanel.WHEN_IN_FOCUSED_WINDOW)
        am = self.getActionMap()
        im.put(copy_key,  "copy");   am.put("copy",  _CopyAction())
        im.put(paste_key, "paste");  am.put("paste", _PasteAction())
        im.put(undo_key_ctrl, "undo"); am.put("undo", _UndoAction())
        im.put(undo_key_meta, "undo")
        im.put(redo_key_ctrl, "redo"); am.put("redo", _RedoAction())
        im.put(redo_key_meta, "redo")
        im.put(up_key,    "up");     am.put("up",    _NudgeAction("y",  -2))
        im.put(down_key,  "down");   am.put("down",  _NudgeAction("y",  +2))
        im.put(left_key,  "left");   am.put("left",  _NudgeAction("x0", -2))
        im.put(right_key, "right");  am.put("right", _NudgeAction("x1", +2))
        im.put(del_key,   "delete"); am.put("delete", _DeleteAction())
        im.put(bsp_key,   "bspace"); am.put("bspace", _DeleteAction())
        class _Mouse(MouseAdapter):
            def mousePressed(self, event):
                canvas.requestFocusInWindow()
                if event.getButton() != MouseEvent.BUTTON1:
                    return
                x, y = event.getX(), event.getY()
                if canvas.mode in ("draw_line", "draw_triangle"):
                    canvas._drag_start = (x, y)
                elif canvas.mode == "sample_label":
                    canvas.ctrl.place_sample_label(x, y)
                elif canvas.mode == "band_annot":
                    canvas.ctrl.place_band_annot(x, y)
                elif canvas.mode == "add_text":
                    canvas.ctrl.place_free_text(x, y)
                    canvas.mode = None
                elif canvas.mode == "edit":
                    target = canvas.ctrl.hit_test(x, y)
                    canvas._drag_target = target
                    canvas._drag_last   = (x, y)
                    if target is not None:
                        canvas.ctrl._record_undo()
                    if target is None:
                        canvas.ctrl.edit_select(x, y)
                elif canvas.mode is None and not canvas.ctrl.edit_mode_active:
                    band = canvas.ctrl.band_hit_test(x, y)
                    if band is not None:
                        canvas.ctrl._record_undo()
                        canvas._drag_band = band
                        canvas._drag_last = (x, y)
                        canvas.ctrl.selected_annot = None
                        canvas.ctrl._set_status("Dragging gel crop")
            def mouseClicked(self, event):
                if canvas.mode == "edit" and event.getClickCount() == 2:
                    canvas.ctrl.rename_selected()
            def mouseDragged(self, event):
                x, y = event.getX(), event.getY()
                if canvas.mode == "draw_line" and canvas._drag_start:
                    canvas.ctrl.preview_draw_line(
                        canvas._drag_start[0], canvas._drag_start[1], x)
                elif canvas.mode == "draw_triangle" and canvas._drag_start:
                    canvas.ctrl.preview_draw_triangle(
                        canvas._drag_start[0], canvas._drag_start[1], x, y)
                elif canvas.mode == "edit" and canvas._drag_target and canvas._drag_last:
                    dx = x - canvas._drag_last[0]
                    dy = y - canvas._drag_last[1]
                    canvas.ctrl.drag_annot(canvas._drag_target, dx, dy)
                    canvas._drag_last = (x, y)
                elif canvas._drag_band is not None and canvas._drag_last:
                    dx = x - canvas._drag_last[0]
                    dy = y - canvas._drag_last[1]
                    canvas.ctrl.drag_band(canvas._drag_band, dx, dy)
                    canvas._drag_last = (x, y)
            def mouseReleased(self, event):
                if canvas.mode == "draw_line" and canvas._drag_start:
                    x0, y0 = canvas._drag_start
                    canvas.ctrl.finish_draw_line(x0, y0, event.getX())
                    canvas._drag_start = None
                elif canvas.mode == "draw_triangle" and canvas._drag_start:
                    x0, y0 = canvas._drag_start
                    canvas.ctrl.finish_draw_triangle(x0, y0,
                                                     event.getX(), event.getY())
                    canvas._drag_start = None
                elif canvas.mode == "edit":
                    canvas.ctrl.sync_fractions_after_drag()
                    canvas._drag_target = None
                    canvas._drag_last   = None
                elif canvas._drag_band is not None:
                    canvas._drag_band = None
                    canvas._drag_last = None
                    canvas.ctrl._clear_status()
        ml = _Mouse()
        self.addMouseListener(ml)
        self.addMouseMotionListener(ml)
    def set_image(self, bi):
        self.bi = bi
        self.setPreferredSize(Dimension(bi.getWidth(), bi.getHeight()))
        self.revalidate()
        self.repaint()
    def paintComponent(self, g):
        super(FigureCanvas, self).paintComponent(g)
        if self.bi:
            g.drawImage(self.bi, 0, 0, None)
class WBTool(ActionListener):
    def __init__(self):
        self._last_dir            = Prefs.get("wbtool.last_dir", None)
        self.bands                = []
        self.hlines               = []
        self.triangles            = []
        self.freetexts            = []
        self.sel_idx              = -1
        self.gel_imp              = None
        self.workflow_mode        = "single"
        self.kda_markers          = []
        self.kda_marker_lanes     = []
        self.kda_mode_active      = False
        self._waiting_for_crop    = False
        self._crop_was_marking    = False
        self._default_label_angle = 45.0
        self.default_font_sizes    = {
            "kda": FONT_KDA.getSize(),
            "protein": FONT_NAME.getSize(),
            "sample": FONT_SAMPLE.getSize(),
            "free": FONT_ANNOT.getSize(),
            "band": FONT_BANDANN.getSize(),
        }
        self.edit_mode_active     = False
        self.selected_annot       = None   # HLine | FreeText | ("sl", band, sl_dict)
        self.clipboard            = None
        self.undo_stack           = []
        self.redo_stack           = []
        self.renderer             = FigureRenderer()
        self._gel_mouse_listener           = None
        self._saved_mouse_listeners        = []
        self._saved_mouse_motion_listeners = []
        self._build_ui()
        self._refresh_figure()
    def _build_ui(self):
        self.frame = JFrame("WBTool — Western Blot Figure Tool")
        self.frame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE)
        self.frame.setLayout(BorderLayout())
        ctrl = JPanel()
        ctrl.setLayout(BoxLayout(ctrl, BoxLayout.Y_AXIS))
        ctrl.setBorder(BorderFactory.createEmptyBorder(8, 8, 8, 8))
        ctrl.setPreferredSize(Dimension(200, 860))
        def section(t):
            lbl = JLabel(t)
            lbl.setFont(Font("Arial", Font.BOLD, 11))
            lbl.setAlignmentX(0.0)
            ctrl.add(lbl);  ctrl.add(JSeparator())
            ctrl.add(Box.createVerticalStrut(4))
        def btn(label, cmd):
            b = JButton(label)
            b.setActionCommand(cmd)
            b.addActionListener(self)
            b.setAlignmentX(0.0)
            b.setMaximumSize(Dimension(190, 28))
            ctrl.add(b);  ctrl.add(Box.createVerticalStrut(3))
            return b
        section("Image")
        btn("Single Image Mode...", "open_image")
        btn("Separate Marker/Blot...", "open_marker_image")
        ctrl.add(Box.createVerticalStrut(6))
        section("kDa Markers")
        self.btn_mark_kda = btn("Mark kDa Bands", "toggle_mark_kda")
        self.btn_mark_kda.setOpaque(True)
        self.btn_apply_markers = btn("Apply Markers to Blot...", "apply_markers_to_blot")
        self.btn_apply_markers.setOpaque(True)
        btn("Undo Last kDa", "undo_kda")
        btn("Clear All kDa", "clear_kda")
        ctrl.add(Box.createVerticalStrut(6))
        section("Crop -> Figure")
        self.btn_crop = btn("Crop Region -> Figure", "crop")
        self.btn_crop.setOpaque(True)
        btn("Show Coordinate Log", "show_coord_log")
        ctrl.add(Box.createVerticalStrut(6))
        section("Bands (select to edit)")
        self.list_model = DefaultListModel()
        self.band_list  = JList(self.list_model)
        self.band_list.setSelectionMode(ListSelectionModel.SINGLE_SELECTION)
        self.band_list.setFont(Font("Arial", Font.PLAIN, 11))
        self.band_list.addListSelectionListener(
            lambda e: self._on_list_select() if not e.getValueIsAdjusting() else None)
        lsp = JScrollPane(self.band_list)
        lsp.setPreferredSize(Dimension(185, 90))
        lsp.setMaximumSize(Dimension(190, 90))
        lsp.setAlignmentX(0.0)
        ctrl.add(lsp);  ctrl.add(Box.createVerticalStrut(4))
        btn("Move Up",    "band_up")
        btn("Move Down",  "band_down")
        btn("Set Width...", "set_width")
        btn("Width +10%", "width_inc")
        btn("Width -10%", "width_dec")
        btn("Remove Band","remove_band")
        ctrl.add(Box.createVerticalStrut(6))
        section("Annotations")
        btn("Draw H-Line (drag)",   "draw_line")
        btn("Draw Triangle (drag)", "draw_triangle")
        self.btn_band_annot = btn("Add Band Tick", "toggle_band_annot")
        self.btn_band_annot.setOpaque(True)
        btn("Add Text (click)",     "add_text")
        self.btn_sample_label = btn("Add Sample Labels", "toggle_sample_label")
        self.btn_sample_label.setOpaque(True)
        self.btn_edit = btn("Edit Annotations", "toggle_edit")
        self.btn_edit.setOpaque(True)
        from java.awt import GridLayout as GL
        dpad = JPanel(GL(3, 3, 2, 2))
        dpad.setMaximumSize(Dimension(90, 68))
        dpad.setAlignmentX(0.0)
        def _dpad_btn(label, cmd):
            b = JButton(label)
            b.setActionCommand(cmd)
            b.addActionListener(self)
            b.setFont(Font("Dialog", Font.PLAIN, 12))
            b.setMargin(awt.Insets(0, 0, 0, 0))
            return b
        empty = lambda: JLabel("")
        dpad.add(empty())
        dpad.add(_dpad_btn("^", "nudge_up"))
        dpad.add(empty())
        dpad.add(_dpad_btn("<", "nudge_x0_left"))
        dpad.add(empty())
        dpad.add(_dpad_btn(">", "nudge_x1_right"))
        dpad.add(empty())
        dpad.add(_dpad_btn("v", "nudge_down"))
        dpad.add(empty())
        ctrl.add(dpad)
        ctrl.add(Box.createVerticalStrut(4))
        size_pad = JPanel(GL(1, 2, 2, 2))
        size_pad.setMaximumSize(Dimension(90, 24))
        size_pad.setAlignmentX(0.0)
        size_pad.add(_dpad_btn("A-", "text_smaller"))
        size_pad.add(_dpad_btn("A+", "text_larger"))
        ctrl.add(size_pad)
        ctrl.add(Box.createVerticalStrut(4))
        btn("Delete Selected","delete_annot")
        ctrl.add(Box.createVerticalStrut(6))
        section("Export")
        btn("Export as PDF...", "export_pdf")
        btn("Export as PNG...", "export_img")
        btn("Clear Figure",     "clear_figure")
        ctrl.add(Box.createVerticalGlue())
        self.status_label = JLabel(" ")
        self.status_label.setFont(Font("Arial", Font.BOLD, 11))
        self.status_label.setForeground(Color(180, 100, 0))
        self.status_label.setAlignmentX(0.0)
        ctrl.add(JSeparator());  ctrl.add(Box.createVerticalStrut(4))
        ctrl.add(self.status_label)
        self.fig_canvas = FigureCanvas(self)
        self.fig_scroll = JScrollPane(self.fig_canvas)
        self.fig_scroll.setPreferredSize(Dimension(750, 860))
        self.frame.add(ctrl,            BorderLayout.WEST)
        self.frame.add(self.fig_scroll, BorderLayout.CENTER)
        self.frame.pack()
        screen = awt.Toolkit.getDefaultToolkit().getScreenSize()
        self.frame.setLocation(0, 0)
        self.frame.setSize(min(self.frame.getWidth(), screen.width // 2),
                           min(self.frame.getHeight(), screen.height))
        self.frame.setVisible(True)
    def _set_status(self, t): self.status_label.setText(t)
    def _clear_status(self):  self.status_label.setText(" ")
    def _snapshot_state(self):
        bands = []
        for b in self.bands:
            bands.append({
                "ref": b,
                "display_w": b.display_w,
                "protein_name": b.protein_name,
                "protein_size": getattr(b, "protein_size", FONT_NAME.getSize()),
                "protein_dx_frac": getattr(b, "protein_dx_frac", 0.0),
                "protein_dy_frac": getattr(b, "protein_dy_frac", 0.0),
                "x_offset": getattr(b, "x_offset", 0.0),
                "y_offset": getattr(b, "y_offset", 0.0),
                "crop_x": getattr(b,"crop_x",None), "crop_y": getattr(b,"crop_y",None),
                "crop_w": getattr(b,"crop_w",None), "crop_h": getattr(b,"crop_h",None),
                "crop_angle": getattr(b,"crop_angle",0.0),
                "kda_markers": [dict(m) for m in b.kda_markers],
                "sample_labels": [dict(sl) for sl in b.sample_labels],
                "band_annots": [dict(ba) for ba in b.band_annots],
            })
        hlines = []
        for hl in self.hlines:
            band_idx = self.bands.index(hl.band_ref) if hl.band_ref in self.bands else None
            hlines.append({
                "x0": hl.x0, "y": hl.y, "x1": hl.x1,
                "band_idx": band_idx,
                "x0_frac": hl.x0_frac, "x1_frac": hl.x1_frac,
                "y_frac": hl.y_frac,
            })
        return {
            "bands": bands,
            "hlines": hlines,
            "triangles": [{
                "x0": t.x0, "y": t.y, "x1": t.x1, "height": t.height,
                "band_idx": self.bands.index(t.band_ref) if t.band_ref in self.bands else None,
                "x0_frac": t.x0_frac, "x1_frac": t.x1_frac,
                "y_frac": t.y_frac, "h_frac": t.h_frac,
            } for t in self.triangles],
            "freetexts": [(ft.x, ft.y, ft.text,
                           getattr(ft, "font_size", FONT_ANNOT.getSize()))
                          for ft in self.freetexts],
        }
    def _restore_state(self, state):
        self.bands = []
        for bs in state["bands"]:
            b = bs["ref"]
            b.display_w = bs["display_w"]
            b.protein_name = bs["protein_name"]
            b.protein_size = bs["protein_size"]
            b.protein_dx_frac = bs["protein_dx_frac"]
            b.protein_dy_frac = bs["protein_dy_frac"]
            b.x_offset = bs.get("x_offset", 0.0)
            b.y_offset = bs.get("y_offset", 0.0)
            b.crop_x=bs.get("crop_x",None); b.crop_y=bs.get("crop_y",None)
            b.crop_w=bs.get("crop_w",None); b.crop_h=bs.get("crop_h",None)
            b.crop_angle=bs.get("crop_angle",0.0)
            b.kda_markers = [dict(m) for m in bs["kda_markers"]]
            b.sample_labels = [dict(sl) for sl in bs["sample_labels"]]
            b.band_annots = [dict(ba) for ba in bs["band_annots"]]
            self.bands.append(b)
        self.hlines = []
        for hs in state["hlines"]:
            band_ref = None
            if hs["band_idx"] is not None and hs["band_idx"] < len(self.bands):
                band_ref = self.bands[hs["band_idx"]]
            self.hlines.append(HLine(hs["x0"], hs["y"], hs["x1"], band_ref,
                                     hs["x0_frac"], hs["x1_frac"],
                                     hs["y_frac"]))
        self.triangles = []
        for ts in state["triangles"]:
            if isinstance(ts, dict):
                band_ref = None
                if ts["band_idx"] is not None and ts["band_idx"] < len(self.bands):
                    band_ref = self.bands[ts["band_idx"]]
                self.triangles.append(TriangleAnnot(
                    ts["x0"], ts["y"], ts["x1"], ts["height"], band_ref,
                    ts["x0_frac"], ts["x1_frac"], ts["y_frac"], ts["h_frac"]))
            else:
                x0, y, x1, h = ts
                self.triangles.append(TriangleAnnot(x0, y, x1, h))
        self.freetexts = []
        for x, y, text, size in state["freetexts"]:
            ft = FreeText(x, y, text)
            ft.font_size = size
            self.freetexts.append(ft)
        self.selected_annot = None
        self.list_model.clear()
        for b in self.bands:
            self.list_model.addElement(b.protein_name)
        self.sel_idx = min(self.sel_idx, len(self.bands) - 1)
        if self.sel_idx >= 0:
            self.band_list.setSelectedIndex(self.sel_idx)
        self._refresh_figure()
    def _record_undo(self):
        self.undo_stack.append(self._snapshot_state())
        if len(self.undo_stack) > 50:
            self.undo_stack.pop(0)
        self.redo_stack = []
    def undo_last_edit(self):
        if not self.undo_stack:
            self._set_status("Nothing to undo")
            return
        self.redo_stack.append(self._snapshot_state())
        state = self.undo_stack.pop()
        self._restore_state(state)
        self._set_status("Undid last edit")
    def redo_last_undo(self):
        if not self.redo_stack:
            self._set_status("Nothing to redo")
            return
        self.undo_stack.append(self._snapshot_state())
        state = self.redo_stack.pop()
        self._restore_state(state)
        self._set_status("Redid edit")
    def _clear_canvas_add_modes(self):
        if hasattr(self, "btn_sample_label"):
            self.btn_sample_label.setBackground(COLOR_INACTIVE)
            self.btn_sample_label.setText("Add Sample Labels")
        if hasattr(self, "btn_band_annot"):
            self.btn_band_annot.setBackground(COLOR_INACTIVE)
            self.btn_band_annot.setText("Add Band Tick")
    def actionPerformed(self, event):
        cmd = event.getActionCommand()
        {
            "open_image":          self.open_image,
            "open_marker_image":   self.open_marker_image,
            "apply_markers_to_blot": self.apply_markers_to_blot,
            "toggle_mark_kda":     self.toggle_mark_kda,
            "undo_kda":            self.undo_last_kda,
            "clear_kda":           self.clear_all_kda,
            "crop":                self.start_crop,
            "show_coord_log":      self.show_coordinate_log,
            "band_up":             lambda: self.move_band(-1),
            "band_down":           lambda: self.move_band(+1),
            "set_width":           self.set_width_dialog,
            "width_inc":           lambda: self.bump_width(1.10),
            "width_dec":           lambda: self.bump_width(1/1.10),
            "remove_band":         self.remove_band,
            "draw_line":           self.enable_draw_line,
            "draw_triangle":       self.enable_draw_triangle,
            "toggle_band_annot":   self.toggle_band_annot,
            "add_text":            self.enable_add_text,
            "toggle_sample_label": self.toggle_sample_label,
            "toggle_edit":         self.toggle_edit_mode,
            "nudge_x0_left":       lambda: self.nudge_annot("x0", -2),
            "nudge_x1_right":      lambda: self.nudge_annot("x1", +2),
            "nudge_up":            lambda: self.nudge_annot("y",  -2),
            "nudge_down":          lambda: self.nudge_annot("y",  +2),
            "text_smaller":        lambda: self.resize_text(-1),
            "text_larger":         lambda: self.resize_text(+1),
            "delete_annot":        self.delete_selected_annot,
            "export_pdf":          self.export_pdf,
            "export_img":          self.export_image,
            "clear_figure":        self.clear_figure,
        }.get(cmd, lambda: None)()
    def open_image(self):
        imp, self._last_dir = open_rgb_image(self.frame, self._last_dir)
        if imp is None:
            return
        if self.kda_mode_active:
            self._deactivate_kda_mode()
        self.workflow_mode = "single"
        self.gel_imp     = imp
        self.kda_markers = []
        show_image_right_half(imp)
        set_crop_selection_tool()
        self._set_status("Single image mode -- mark kDa bands or crop directly")
    def open_marker_image(self):
        imp, self._last_dir = open_rgb_image(self.frame, self._last_dir)
        if imp is None:
            return
        if self.kda_mode_active:
            self._deactivate_kda_mode()
        self.workflow_mode = "paired_marker"
        self.gel_imp = imp
        self.kda_markers = []
        show_image_right_half(imp)
        self._activate_kda_mode()
        self._set_status("Paired mode -- mark the marker image, then apply markers to blot")
    def apply_markers_to_blot(self):
        if self.workflow_mode not in ("paired_marker","paired_blot"):
            JOptionPane.showMessageDialog(self.frame,
                "Start with Separate Marker/Blot, then mark the ladder bands.",
                "Not in paired mode", JOptionPane.WARNING_MESSAGE)
            return
        if not self.kda_markers:
            JOptionPane.showMessageDialog(self.frame,
                "Mark at least one kDa band on the marker image first.",
                "No markers", JOptionPane.WARNING_MESSAGE)
            return
        marker_w = self.gel_imp.getWidth() if self.gel_imp is not None else None
        marker_h = self.gel_imp.getHeight() if self.gel_imp is not None else None
        self._remember_kda_lane()
        was_marking = self.kda_mode_active
        if self.kda_mode_active:
            self._deactivate_kda_mode()
        imp, self._last_dir = open_rgb_image(self.frame, self._last_dir)
        if imp is None:
            if was_marking: self._activate_kda_mode()
            return
        if marker_w is not None and (imp.getWidth() != marker_w or imp.getHeight() != marker_h):
            JOptionPane.showMessageDialog(self.frame,
                "The marker and blot images should have the same width and height.",
                "Image size mismatch", JOptionPane.WARNING_MESSAGE)
        self.workflow_mode = "paired_blot"
        self.gel_imp = imp
        show_image_right_half(imp)
        self._redraw_kda_overlay()
        set_crop_selection_tool()
        self._set_status("Markers applied to blot -- draw a crop, rotate if needed, then confirm")
    def toggle_mark_kda(self):
        if self.gel_imp is None:
            JOptionPane.showMessageDialog(self.frame,
                "Open a gel image first.", "No image",
                JOptionPane.WARNING_MESSAGE)
            return
        if self.kda_mode_active: self._deactivate_kda_mode()
        else:                    self._activate_kda_mode()
    def _activate_kda_mode(self):
        self.kda_mode_active = True
        self.btn_mark_kda.setBackground(COLOR_ACTIVE)
        self.btn_mark_kda.setText("Stop Marking kDa")
        self._set_status("kDa marking active -- click gel")
        IJ.setTool("point")
        canvas = self.gel_imp.getCanvas()
        if canvas is None: return
        self._saved_mouse_listeners = canvas.getMouseListeners()
        for ml in self._saved_mouse_listeners:
            canvas.removeMouseListener(ml)
        self._saved_mouse_motion_listeners = canvas.getMouseMotionListeners()
        for ml in self._saved_mouse_motion_listeners:
            canvas.removeMouseMotionListener(ml)
        ctrl = self
        class _KdaMouse(MouseAdapter):
            def mousePressed(self, event):
                if not ctrl.kda_mode_active: return
                if event.getButton() != MouseEvent.BUTTON1: return
                event.consume()
                ic = ctrl.gel_imp.getCanvas()
                ctrl._on_gel_click(float(ic.offScreenX(event.getX())),float(ic.offScreenY(event.getY())))
        self._gel_mouse_listener = _KdaMouse()
        canvas.addMouseListener(self._gel_mouse_listener)
    def _deactivate_kda_mode(self):
        self.kda_mode_active = False
        self.btn_mark_kda.setBackground(COLOR_INACTIVE)
        self.btn_mark_kda.setText("Mark kDa Bands")
        self._clear_status()
        if self.gel_imp is not None:
            canvas = self.gel_imp.getCanvas()
            if canvas is not None:
                if self._gel_mouse_listener is not None:
                    canvas.removeMouseListener(self._gel_mouse_listener)
                for ml in self._saved_mouse_listeners:
                    canvas.addMouseListener(ml)
                for ml in self._saved_mouse_motion_listeners:
                    canvas.addMouseMotionListener(ml)
        self._gel_mouse_listener           = None
        self._saved_mouse_listeners        = []
        self._saved_mouse_motion_listeners = []
        set_crop_selection_tool()
    def _on_gel_click(self, scene_x, scene_y):
        val = ask_string("kDa value", "Enter kDa label for this band:", "0")
        if val is None:
            return
        val = val.strip()
        if not val:
            JOptionPane.showMessageDialog(self.frame,
                "Please enter a kDa label.", "Invalid kDa",
                JOptionPane.WARNING_MESSAGE)
            return
        self.kda_markers.append({"x_abs":scene_x,"y_orig": scene_y, "y_abs":scene_y, "kda": val,
                                 "font_size": self.default_font_sizes["kda"]})
        self.kda_markers.sort(key=lambda d: d["y_orig"])
        self._redraw_kda_overlay()
        n = len(self.kda_markers)
        self._set_status("kDa marking active -- %d mark%s" % (n, "s" if n!=1 else ""))
    def _redraw_kda_overlay(self):
        if self.gel_imp is None: return
        ov = Overlay()
        for m in self.kda_markers:
            y = m["y_orig"];  x1 = -2.0;  x0 = x1 - TICK_LEN
            tick = Line(x0, y, x1, y)
            tick.setStrokeColor(Color.RED);  tick.setStrokeWidth(1.5)
            ov.add(tick)
            lbl = TextRoi(x0 - 35, y - 7, kda_label_text(m["kda"]), FONT_KDA)
            lbl.setStrokeColor(Color.RED);  ov.add(lbl)
        self.gel_imp.setOverlay(ov);  self.gel_imp.updateAndDraw()
    def undo_last_kda(self):
        if not self.kda_markers: return
        self.kda_markers.pop();  self._redraw_kda_overlay()
        if self.kda_mode_active:
            n = len(self.kda_markers)
            self._set_status("kDa marking active -- %d mark%s" % (n, "s" if n!=1 else ""))
    def clear_all_kda(self):
        self.kda_markers = [];  self._redraw_kda_overlay()
        if self.kda_mode_active:
            self._set_status("kDa marking active -- click gel")
    def _fc(self,v):
        return "NA" if v is None else ("%.2f"%v if isinstance(v,float) else str(v))
    def _same_lane(self,a,b):
        if len(a)!=len(b): return False
        for x,y in zip(a,b):
            if x.get("kda")!=y.get("kda"): return False
            if self._fc(x.get("x_abs",None))!=self._fc(y.get("x_abs",None)): return False
            if self._fc(x.get("y_abs",x.get("y_orig",None)))!=self._fc(y.get("y_abs",y.get("y_orig",None))): return False
        return True
    def _remember_kda_lane(self):
        if not self.kda_markers: return
        lane=[dict(m) for m in self.kda_markers]
        if not self.kda_marker_lanes or not self._same_lane(self.kda_marker_lanes[-1],lane):
            self.kda_marker_lanes.append(lane)
    def coordinate_log_text(self):
        a=["WBTool Coordinate Log",""]
        if self.gel_imp is not None:
            a+=["Source image: "+self.gel_imp.getTitle(),"Source size: width=%d, height=%d"%(self.gel_imp.getWidth(),self.gel_imp.getHeight()),""]
        a.append("Global kDa markers (absolute source-image coordinates):")
        lanes=[list(l) for l in self.kda_marker_lanes]
        if self.kda_markers and (not lanes or not self._same_lane(lanes[-1],self.kda_markers)):
            lanes.append(self.kda_markers)
        if lanes:
            for li,lane in enumerate(lanes):
                a.append("  Lane %d:"%(li+1))
                for i,m in enumerate(lane):
                    a.append("    %d. label=%s, x_abs=%s, y_abs=%s"%(i+1,kda_label_text(m["kda"]),self._fc(m.get("x_abs",None)),self._fc(m.get("y_abs",m.get("y_orig",None)))))
        else: a.append("  none")
        a+=["","Crops in figure:"]
        if self.bands:
            for i,b in enumerate(self.bands):
                ml="none"
                if b.kda_markers:
                    for li,lane in enumerate(lanes):
                        ok=True
                        for bm in b.kda_markers:
                            hit=False
                            for m in lane:
                                if bm.get("kda")==m.get("kda") and self._fc(bm.get("x_abs",None))==self._fc(m.get("x_abs",None)) and self._fc(bm.get("y_abs",None))==self._fc(m.get("y_abs",m.get("y_orig",None))):
                                    hit=True; break
                            if not hit:
                                ok=False; break
                        if ok:
                            ml=str(li+1); break
                a.append("  Band %d: marker lane %s, %s"%(i+1,ml,plain_text(b.protein_name)))
                a.append("    crop_abs: x=%s, y=%s, width=%s, height=%s, angle=%s"%(self._fc(getattr(b,"crop_x",None)),self._fc(getattr(b,"crop_y",None)),self._fc(getattr(b,"crop_w",None)),self._fc(getattr(b,"crop_h",None)),self._fc(getattr(b,"crop_angle",0.0))))
                if b.kda_markers:
                    for m in b.kda_markers:
                        a.append("      label=%s, x_abs=%s, y_abs=%s, y_in_crop=%s"%(kda_label_text(m["kda"]),self._fc(m.get("x_abs",None)),self._fc(m.get("y_abs",None)),self._fc(m.get("y_orig",None))))
                else: a.append("      kDa markers: none")
        else: a.append("  none")
        return "\n".join(a)
    def show_coordinate_log(self):
        t=JTextArea(self.coordinate_log_text(),24,70); t.setEditable(False); t.setLineWrap(False)
        sp=JScrollPane(t); sp.setPreferredSize(Dimension(700,420))
        JOptionPane.showMessageDialog(self.frame,sp,"Coordinate Log",JOptionPane.INFORMATION_MESSAGE)
    def start_crop(self):
        if self.gel_imp is None:
            JOptionPane.showMessageDialog(self.frame, "Open a gel image first.",
                "No image", JOptionPane.WARNING_MESSAGE)
            return
        if not self._waiting_for_crop:
            self._waiting_for_crop = True
            self._crop_was_marking = self.kda_mode_active
            if self.kda_mode_active: self._deactivate_kda_mode()
            set_crop_selection_tool()
            self.btn_crop.setBackground(COLOR_ACTIVE)
            self.btn_crop.setText("Confirm Crop")
            self._set_status("Draw a crop on the gel; rotate it if needed, then click Confirm Crop")
            return
        self._waiting_for_crop = False
        self.btn_crop.setBackground(COLOR_INACTIVE)
        self.btn_crop.setText("Crop Region -> Figure")
        self._clear_status()
        roi = self.gel_imp.getRoi()
        if roi is None:
            JOptionPane.showMessageDialog(self.frame,
                "No selection found. Click Crop again and draw first.",
                "No selection", JOptionPane.WARNING_MESSAGE)
            if self._crop_was_marking: self._activate_kda_mode()
            return
        crop_data = rotated_crop_from_roi(self.gel_imp, roi)
        if crop_data is None:
            JOptionPane.showMessageDialog(self.frame,
                "Selection too small -- please try again.",
                "Too small", JOptionPane.WARNING_MESSAGE)
            if self._crop_was_marking: self._activate_kda_mode()
            return
        cropped, x, y, w, h, angle = crop_data
        self._remember_kda_lane()
        local_m = []
        for m in self.kda_markers:
            yy = marker_y_in_crop(m, x, y, angle)
            if -0.5 <= yy <= h + 0.5:
                local_m.append({"y_orig": yy,
                                "x_abs": m.get("x_abs", None),
                                "y_abs": m.get("y_abs", m.get("y_orig", None)),
                                "crop_angle": angle,
                                "kda": m["kda"],
                                "font_size": m.get("font_size",
                                                   self.default_font_sizes["kda"])})
        local_m.sort(key=lambda d: d["y_orig"])
        protein = ask_string("Protein name", "Enter protein name:", "Protein")
        if protein is None:
            if self._crop_was_marking: self._activate_kda_mode()
            return
        band = Band(cropped, local_m, protein or "Protein",
                    width=self.bands[-1].display_w if self.bands else None)
        band.protein_size = self.default_font_sizes["protein"]
        band.crop_x=x; band.crop_y=y; band.crop_w=w; band.crop_h=h
        band.crop_angle=angle
        self._record_undo()
        self.bands.append(band)
        self.list_model.addElement(protein or "Protein")
        self.band_list.setSelectedIndex(len(self.bands) - 1)
        self._refresh_figure()
        if self._crop_was_marking: self._activate_kda_mode()
    def _on_list_select(self):
        self.sel_idx = self.band_list.getSelectedIndex()
    def _triangle_anchor_y(self, tri):
        return max(y for x, y in tri.points())
    def _band_triangle_zone(self, idx):
        rect = self.renderer.band_img_rect(idx, self.bands)
        if rect is None:
            return None
        ix, iy, dw, dh = rect
        top = 0.0
        bottom = float(iy + dh + self.renderer.band_extra_bottom(self.bands[idx]) + BAND_GAP)
        if idx > 0:
            prev = self.renderer.band_img_rect(idx - 1, self.bands)
            if prev is not None:
                top = (prev[1] + prev[3] + iy) / 2.0
        if idx + 1 < len(self.bands):
            nxt = self.renderer.band_img_rect(idx + 1, self.bands)
            if nxt is not None:
                bottom = (iy + dh + nxt[1]) / 2.0
        return top, bottom
    def _triangle_band_index(self, tri):
        ay = self._triangle_anchor_y(tri)
        for idx in range(len(self.bands)):
            zone = self._band_triangle_zone(idx)
            if zone is None:
                continue
            top, bottom = zone
            if top <= ay <= bottom:
                return idx
        return None
    def move_band(self, direction):
        i = self.sel_idx
        if i < 0: return
        j = i + direction
        if j < 0 or j >= len(self.bands): return
        old_tri_bands = {}
        old_rects = {}
        for idx in (i, j):
            rect = self.renderer.band_img_rect(idx, self.bands)
            if rect is not None:
                old_rects[self.bands[idx]] = rect
        for tri in self.triangles:
            idx = self._triangle_band_index(tri)
            if idx in (i, j):
                old_tri_bands[tri] = self.bands[idx]
        self._record_undo()
        self.bands[i], self.bands[j] = self.bands[j], self.bands[i]
        a, b = self.list_model.get(i), self.list_model.get(j)
        self.list_model.set(i, b);  self.list_model.set(j, a)
        for tri, band in old_tri_bands.items():
            if band in self.bands and band in old_rects:
                new_rect = self.renderer.band_img_rect(self.bands.index(band), self.bands)
                if new_rect is not None:
                    tri.y += new_rect[1] - old_rects[band][1]
        self.band_list.setSelectedIndex(j);  self.sel_idx = j
        self._refresh_figure()
    def remove_band(self):
        i = self.sel_idx
        if i < 0 or i >= len(self.bands): return
        self._record_undo()
        removed = self.bands.pop(i)
        for hl in self.hlines:
            if hl.band_ref is removed:
                hl.band_ref = None
        self.list_model.remove(i)
        self.sel_idx = min(i, len(self.bands) - 1)
        self.band_list.setSelectedIndex(self.sel_idx)
        self._refresh_figure()
    def _sel_band(self):
        return self.bands[self.sel_idx] if 0 <= self.sel_idx < len(self.bands) else None
    def bump_width(self, factor):
        b = self._sel_band()
        if b is None: return
        self._record_undo()
        b.display_w = max(10, int(b.display_w * factor));  self._refresh_figure()
    def set_width_dialog(self):
        b = self._sel_band()
        if b is None: return
        val = ask_int("Set width", "Width (pixels):", b.display_w)
        if val and val > 0:
            self._record_undo()
            b.display_w = val;  self._refresh_figure()
    def toggle_sample_label(self):
        if not self.bands: return
        if self.fig_canvas.mode == "sample_label":
            self._deactivate_sample_label_mode()
        else:
            self._activate_sample_label_mode()
    def _activate_sample_label_mode(self):
        self._clear_canvas_add_modes()
        self.fig_canvas.mode = "sample_label"
        self.btn_sample_label.setBackground(COLOR_ACTIVE)
        self.btn_sample_label.setText("Stop Adding Labels")
        self._set_status("Label mode -- click a lane to add label")
    def _deactivate_sample_label_mode(self):
        self.fig_canvas.mode = None
        self.btn_sample_label.setBackground(COLOR_INACTIVE)
        self.btn_sample_label.setText("Add Sample Labels")
        self._clear_status()
    def place_sample_label(self, px, py):
        if not self.bands: return
        text = ask_string("Sample name", "Enter sample name:", "Sample")
        if not text:
            self._deactivate_sample_label_mode();  return
        angle = ask_float("Label angle", "Tilt angle (degrees):",
                          self._default_label_angle)
        if angle is None:
            self._deactivate_sample_label_mode();  return
        self._default_label_angle = angle
        for i, b in enumerate(self.bands):
            rect = self.renderer.band_img_rect(i, self.bands)
            if rect is None:
                continue
            ix, iy, dw, dh = rect
            if iy - TOP_MARGIN <= py <= iy + dh:
                x_frac = max(0.0, min(1.0,
                    float(px - ix) / float(dw)))
                self._record_undo()
                b.sample_labels.append({"x_frac": x_frac,
                                        "text":   text,
                                        "angle":  float(angle),
                                        "font_size": self.default_font_sizes["sample"]})
                break
        n = sum(len(b.sample_labels) for b in self.bands)
        self._set_status("Label mode -- %d label%s  (click to add more)" % (
            n, "s" if n != 1 else ""))
        self._refresh_figure()
    def enable_draw_line(self):
        self._clear_canvas_add_modes()
        self.fig_canvas.mode = "draw_line"
        self._set_status("Drag on figure to draw a horizontal line")
    def enable_draw_triangle(self):
        self._clear_canvas_add_modes()
        self.fig_canvas.mode = "draw_triangle"
        self._set_status("Drag on figure to draw a black triangle")
    def _band_at_y(self, py):
        for i, b in enumerate(self.bands):
            rect = self.renderer.band_img_rect(i, self.bands)
            if rect is None:
                continue
            ix, iy, dw, dh = rect
            if iy <= py <= iy + dh:
                return b, ix, iy, dw, dh
        return None, 0, 0, 0, 0
    def band_hit_test(self, px, py):
        for i in range(len(self.bands) - 1, -1, -1):
            rect = self.renderer.band_img_rect(i, self.bands)
            if rect is None:
                continue
            ix, iy, dw, dh = rect
            if ix <= px <= ix + dw and iy <= py <= iy + dh:
                self.sel_idx = i
                self.band_list.setSelectedIndex(i)
                return self.bands[i]
        return None
    def drag_band(self, band, dx, dy):
        if band is None:
            return
        band.y_offset = getattr(band, "y_offset", 0.0) + dy
        self._refresh_figure()
    def preview_draw_line(self, x0, y0, x1):
        self._refresh_figure(preview_line=(min(x0,x1), y0, max(x0,x1)))
    def finish_draw_line(self, x0, y0, x1):
        if abs(x1 - x0) < 3:
            self._refresh_figure();  return
        lx0 = min(x0, x1);  lx1 = max(x0, x1)
        band, img_x, img_y, dw, dh = self._band_at_y(y0)
        if band is not None and dw > 0 and dh > 0:
            hl = HLine(lx0, y0, lx1, band_ref=band,
                       x0_frac=(lx0-img_x)/float(dw),
                       x1_frac=(lx1-img_x)/float(dw),
                       y_frac =(y0 -img_y)/float(dh))
        else:
            hl = HLine(lx0, y0, lx1)
        self._record_undo()
        self.hlines.append(hl)
        self.fig_canvas.mode = None;  self._clear_status()
        self._refresh_figure()
    def preview_draw_triangle(self, x0, y0, x1, y1):
        height = max(4.0, abs(float(y1) - float(y0)))
        self._refresh_figure(preview_triangle=TriangleAnnot(x0, y0, x1,
                                                            height))
    def finish_draw_triangle(self, x0, y0, x1, y1):
        if abs(x1 - x0) < 3:
            self._refresh_figure();  return
        height = max(4.0, abs(float(y1) - float(y0)))
        tri = TriangleAnnot(x0, y0, x1, height)
        band_idx = self._triangle_band_index(tri)
        if band_idx is not None:
            rect = self.renderer.band_img_rect(band_idx, self.bands)
            if rect is not None:
                img_x, img_y, dw, dh = rect
                tri.band_ref = self.bands[band_idx]
                if dw > 0:
                    tri.x0_frac = (tri.x0 - img_x) / float(dw)
                    tri.x1_frac = (tri.x1 - img_x) / float(dw)
                if dh > 0:
                    tri.y_frac = (tri.y - img_y) / float(dh)
                    tri.h_frac = tri.height / float(dh)
        self._record_undo()
        self.triangles.append(tri)
        self.fig_canvas.mode = None;  self._clear_status()
        self._refresh_figure()
    def toggle_band_annot(self):
        if not self.bands: return
        if self.fig_canvas.mode == "band_annot":
            self._deactivate_band_annot_mode()
        else:
            self._activate_band_annot_mode()
    def _activate_band_annot_mode(self):
        self._clear_canvas_add_modes()
        self.fig_canvas.mode = "band_annot"
        self.btn_band_annot.setBackground(COLOR_ACTIVE)
        self.btn_band_annot.setText("Stop Adding Ticks")
        self._set_status("Band tick mode -- click a crop at the band height")
    def _deactivate_band_annot_mode(self):
        self.fig_canvas.mode = None
        self.btn_band_annot.setBackground(COLOR_INACTIVE)
        self.btn_band_annot.setText("Add Band Tick")
        self._clear_status()
    def place_band_annot(self, px, py):
        band, img_x, img_y, dw, dh = self._band_at_y(py)
        if band is None or dh <= 0:
            self._set_status("Band tick mode -- click inside a crop")
            return
        text = ask_string("Band annotation", "Enter text:", "")
        if not text:
            self._deactivate_band_annot_mode();  return
        y_frac = max(0.0, min(1.0, float(py - img_y) / float(dh)))
        self._record_undo()
        band.band_annots.append({"y_frac": y_frac, "text": text,
                                 "font_size": self.default_font_sizes["band"]})
        n = sum(len(b.band_annots) for b in self.bands)
        self._set_status("Band tick mode -- %d tick%s  (click to add more)" % (
            n, "s" if n != 1 else ""))
        self._refresh_figure()
    def enable_add_text(self):
        self._clear_canvas_add_modes()
        self.fig_canvas.mode = "add_text"
        self._set_status("Click on figure to place text")
    def place_free_text(self, px, py):
        text = ask_string("Annotation text", "Enter text:", "")
        if not text:
            self._clear_status();  return
        ft = FreeText(px, py, text)
        ft.font_size = self.default_font_sizes["free"]
        self._record_undo()
        self.freetexts.append(ft)
        self.fig_canvas.mode = None;  self._clear_status()
        self._refresh_figure()
    def toggle_edit_mode(self):
        if self.edit_mode_active: self._deactivate_edit_mode()
        else:                     self._activate_edit_mode()
    def _activate_edit_mode(self):
        self._clear_canvas_add_modes()
        self.edit_mode_active = True
        self.btn_edit.setBackground(COLOR_ACTIVE)
        self.btn_edit.setText("Stop Editing")
        self.fig_canvas.mode = "edit"
        self._set_status("Edit mode -- click to select, drag to move")
        self._refresh_figure()
    def _deactivate_edit_mode(self):
        self.edit_mode_active = False
        self.selected_annot   = None
        self.btn_edit.setBackground(COLOR_INACTIVE)
        self.btn_edit.setText("Edit Annotations")
        self.fig_canvas.mode = None
        self._clear_status();  self._refresh_figure()
    def _iter_sl(self):
        """Iterate all (band, sl_dict, ix, iy, dw) for all sample labels."""
        for i, b in enumerate(self.bands):
            rect = self.renderer.band_img_rect(i, self.bands)
            if rect is None:
                continue
            ix, iy, dw, dh = rect
            for sl in b.sample_labels:
                yield b, sl, ix, iy, dw
    def _iter_ba(self):
        """Iterate all (band, ba_dict, ix, iy, dw, dh) for band annotations."""
        for i, b in enumerate(self.bands):
            rect = self.renderer.band_img_rect(i, self.bands)
            if rect is None:
                continue
            ix, iy, dw, dh = rect
            for ba in b.band_annots:
                yield b, ba, ix, iy, dw, dh
    def _band_annot_hit(self, ba, ix, iy, dw, dh, px, py):
        ty = iy + ba["y_frac"] * dh
        x0 = ix + dw + 2
        x1 = x0 + TICK_LEN
        text_w = HIT_RADIUS * 8
        if self.fig_canvas.bi is not None:
            g = self.fig_canvas.bi.createGraphics()
            g.setFont(sized_font(FONT_BANDANN,
                                  ba.get("font_size", FONT_BANDANN.getSize())))
            text_w = rich_text_width(g, g.getFont(), ba["text"])
            g.dispose()
        if x0 - BA_HIT_R <= px <= x1 + BA_HIT_R and abs(py - ty) <= BA_HIT_R:
            return True
        tx = x1 + TICK_GAP
        if tx - 2 <= px <= tx + text_w + 4 and ty - BA_HIT_R <= py <= ty + BA_HIT_R:
            return True
        return False
    def _kda_hit(self, m, ix, iy, sc, px, py):
        ty = iy + m["y_orig"] * sc
        x1 = ix - 2
        x0 = x1 - TICK_LEN
        lbl = kda_label_text(m["kda"])
        text_w = HIT_RADIUS * 4
        text_h = FONT_KDA.getSize()
        if self.fig_canvas.bi is not None:
            g = self.fig_canvas.bi.createGraphics()
            g.setFont(sized_font(FONT_KDA,
                                  m.get("font_size", FONT_KDA.getSize())))
            fm = g.getFontMetrics()
            text_w = fm.stringWidth(lbl)
            text_h = fm.getHeight()
            g.dispose()
        tx0 = x0 - TICK_GAP - text_w
        if x0 - BA_HIT_R <= px <= x1 + BA_HIT_R and abs(py - ty) <= BA_HIT_R:
            return True
        if tx0 - 2 <= px <= x0 - TICK_GAP + 2 and ty - text_h <= py <= ty + text_h:
            return True
        return False
    def _protein_hit(self, b, ix, iy, dw, dh, px, py):
        text_w = HIT_RADIUS * 8
        text_h = FONT_NAME.getSize()
        if self.fig_canvas.bi is not None:
            g = self.fig_canvas.bi.createGraphics()
            g.setFont(sized_font(FONT_NAME, getattr(b, "protein_size",
                                                     FONT_NAME.getSize())))
            fm = g.getFontMetrics()
            text_w = rich_text_width(g, g.getFont(), b.protein_name)
            text_h = fm.getHeight() * max(1, len(rich_text_lines(b.protein_name)))
            g.dispose()
        if b.band_annots:
            tx = ix + dw // 2 - text_w // 2
            ty = iy + dh + text_h + 5
        else:
            tx = ix + dw + 10
            ty = iy + dh // 2 + text_h // 2
        tx += int(round(getattr(b, "protein_dx_frac", 0.0) * dw))
        ty += int(round(getattr(b, "protein_dy_frac", 0.0) * dh))
        return tx - 2 <= px <= tx + text_w + 2 and ty - text_h <= py <= ty + 4
    def _free_text_rect(self, ft):
        text_w = HIT_RADIUS * 6
        text_h = FONT_ANNOT.getSize()
        if self.fig_canvas.bi is not None:
            g = self.fig_canvas.bi.createGraphics()
            ft_font = sized_font(FONT_ANNOT,
                                  getattr(ft, "font_size", FONT_ANNOT.getSize()))
            g.setFont(ft_font)
            rect = rich_text_block_rect(g, ft_font, ft.x, ft.y, ft.text)
            g.dispose()
            return rect
        return (ft.x - 2, ft.y - text_h, text_w + 4, text_h + 4)
    def _free_text_hit(self, ft, px, py):
        x, y, w, h = self._free_text_rect(ft)
        return x <= px <= x + w and y <= py <= y + h
    def _tri_area(self, ax, ay, bx, by, cx, cy):
        return abs((ax*(by-cy) + bx*(cy-ay) + cx*(ay-by)) / 2.0)
    def _tri_contains(self, tri, px, py):
        pts = tri.points()
        (ax, ay), (bx, by), (cx, cy) = pts
        a = self._tri_area(ax, ay, bx, by, cx, cy)
        a1 = self._tri_area(px, py, bx, by, cx, cy)
        a2 = self._tri_area(ax, ay, px, py, cx, cy)
        a3 = self._tri_area(ax, ay, bx, by, px, py)
        return abs(a - (a1 + a2 + a3)) <= 1.0
    def _tri_hit(self, tri, px, py):
        pts = tri.points()
        tall_top, tall_base, short_base = pts
        if dist2(px, py, tall_top[0], tall_top[1]) <= HIT_RADIUS:
            return "tri_top"
        if dist2(px, py, tall_base[0], tall_base[1]) <= HIT_RADIUS:
            return "tri_bottom"
        if dist2(px, py, short_base[0], short_base[1]) <= HIT_RADIUS:
            return "tri_tip"
        if self._tri_contains(tri, px, py):
            return "tri_body"
        return None
    def hit_test(self, px, py):
        a = self.selected_annot
        if a is None:
            return None
        hs = HANDLE_SIZE
        if isinstance(a, HLine):
            if abs(px - a.x0) <= hs and abs(py - a.y) <= hs:
                return "h_x0"
            if abs(px - a.x1) <= hs and abs(py - a.y) <= hs:
                return "h_x1"
            if a.x0 <= px <= a.x1 and abs(py - a.y) <= HIT_RADIUS:
                return "h_body"
        elif isinstance(a, TriangleAnnot):
            return self._tri_hit(a, px, py)
        elif isinstance(a, FreeText):
            if self._free_text_hit(a, px, py):
                return "ft_body"
        elif isinstance(a, tuple) and a[0] == "sl":
            _, b, sl = a
            idx = self.bands.index(b) if b in self.bands else -1
            rect = self.renderer.band_img_rect(idx, self.bands) if idx >= 0 else None
            if rect is not None:
                ix, iy, dw, dh = rect
                ax, ay = sl_anchor(sl, ix, iy, dw)
                if dist2(px, py, ax, ay) <= SL_HIT_R:
                    return "sl_body"
        elif isinstance(a, tuple) and a[0] == "ba":
            _, b, ba = a
            idx = self.bands.index(b) if b in self.bands else -1
            rect = self.renderer.band_img_rect(idx, self.bands) if idx >= 0 else None
            if rect is not None:
                ix, iy, dw, dh = rect
                if self._band_annot_hit(ba, ix, iy, dw, dh, px, py):
                    return "ba_body"
        elif isinstance(a, tuple) and a[0] == "kda":
            _, b, m = a
            idx = self.bands.index(b) if b in self.bands else -1
            rect = self.renderer.band_img_rect(idx, self.bands) if idx >= 0 else None
            if rect is not None:
                ix, iy, dw, dh = rect
                if self._kda_hit(m, ix, iy, b.scale(), px, py):
                    return "kda_body"
        elif isinstance(a, tuple) and a[0] == "protein":
            _, b = a
            idx = self.bands.index(b) if b in self.bands else -1
            rect = self.renderer.band_img_rect(idx, self.bands) if idx >= 0 else None
            if rect is not None:
                ix, iy, dw, dh = rect
                if self._protein_hit(b, ix, iy, dw, dh, px, py):
                    return "protein_body"
        return None
    def edit_select(self, px, py):
        best = None;  best_dist = HIT_RADIUS + 1
        for hl in self.hlines:
            cx   = max(hl.x0, min(float(px), hl.x1))
            dist = dist2(float(px), float(py), cx, hl.y)
            if dist < best_dist:
                best_dist = dist;  best = hl
        for tri in self.triangles:
            target = self._tri_hit(tri, px, py)
            if target is not None:
                dist = 0 if target == "tri_body" else HIT_RADIUS - 1
                if dist < best_dist:
                    best_dist = dist;  best = tri
        for ft in self.freetexts:
            if self._free_text_hit(ft, px, py):
                x, y, w, h = self._free_text_rect(ft)
                dist = dist2(float(px), float(py), x + w / 2.0, y + h / 2.0)
                if best is None or not isinstance(best, FreeText) or dist < best_dist:
                    best_dist = dist;  best = ft
        for b, sl, ix, iy, dw in self._iter_sl():
            ax, ay = sl_anchor(sl, ix, iy, dw)
            dist = dist2(float(px), float(py), ax, ay)
            if dist < best_dist:
                best_dist = dist;  best = ("sl", b, sl)
        for b, ba, ix, iy, dw, dh in self._iter_ba():
            if self._band_annot_hit(ba, ix, iy, dw, dh, px, py):
                ty = iy + ba["y_frac"] * dh
                dist = abs(float(py) - ty)
                if dist < best_dist:
                    best_dist = dist;  best = ("ba", b, ba)
        for i, b in enumerate(self.bands):
            rect = self.renderer.band_img_rect(i, self.bands)
            if rect is None:
                continue
            ix, iy, dw, dh = rect
            for m in b.kda_markers:
                if self._kda_hit(m, ix, iy, b.scale(), px, py):
                    ty = iy + m["y_orig"] * b.scale()
                    dist = abs(float(py) - ty)
                    if dist < best_dist:
                        best_dist = dist;  best = ("kda", b, m)
            if self._protein_hit(b, ix, iy, dw, dh, px, py):
                if best is None:
                    best_dist = 0;  best = ("protein", b)
        self.selected_annot = best
        if best is None:
            self._set_status("Edit mode -- click to select")
        elif isinstance(best, HLine):
            self._set_status("Selected: H-Line  |  drag handles or body")
        elif isinstance(best, TriangleAnnot):
            self._set_status("Selected: triangle  |  drag body or handles")
        elif self._is_text_selection(best):
            self._set_status(self._text_selection_status(best))
        self._refresh_figure()
    def drag_annot(self, target, dx, dy):
        a = self.selected_annot
        if a is None: return
        if target == "h_x0" and isinstance(a, HLine):
            a.x0 = min(a.x0 + dx, a.x1 - 2)
        elif target == "h_x1" and isinstance(a, HLine):
            a.x1 = max(a.x1 + dx, a.x0 + 2)
        elif target == "h_body" and isinstance(a, HLine):
            a.x0 += dx;  a.x1 += dx;  a.y += dy
        elif isinstance(a, TriangleAnnot):
            if target == "tri_body":
                a.x0 += dx;  a.x1 += dx;  a.y += dy
            elif target == "tri_tip":
                a.x1 += dx
            elif target == "tri_top":
                a.x0 += dx
                a.y += dy
                a.height = max(4.0, a.height - dy)
            elif target == "tri_bottom":
                a.x0 += dx
                a.height = max(4.0, a.height + dy)
            self._sync_triangle_fractions(a)
        elif target == "ft_body" and isinstance(a, FreeText):
            a.x += dx;  a.y += dy
        elif target == "ba_body" and isinstance(a, tuple) and a[0] == "ba":
            _, b, ba = a
            idx = self.bands.index(b) if b in self.bands else -1
            rect = self.renderer.band_img_rect(idx, self.bands) if idx >= 0 else None
            if rect is not None:
                img_x, img_y, dw, dh = rect
                cur_y = img_y + ba["y_frac"] * dh
                new_y = max(img_y, min(img_y + dh, cur_y + dy))
                if dh > 0:
                    ba["y_frac"] = (new_y - img_y) / float(dh)
        elif target == "protein_body" and isinstance(a, tuple) and a[0] == "protein":
            _, b = a
            idx = self.bands.index(b) if b in self.bands else -1
            rect = self.renderer.band_img_rect(idx, self.bands) if idx >= 0 else None
            if rect is not None:
                img_x, img_y, dw, dh = rect
                if dw > 0:
                    b.protein_dx_frac = getattr(b, "protein_dx_frac", 0.0) + dx / float(dw)
                if dh > 0:
                    b.protein_dy_frac = getattr(b, "protein_dy_frac", 0.0) + dy / float(dh)
        self._refresh_figure()
    def sync_fractions_after_drag(self):
        a = self.selected_annot
        if a is None: return
        if isinstance(a, HLine):
            self._sync_hline_fractions(a)
        elif isinstance(a, TriangleAnnot):
            self._sync_triangle_fractions(a)
    def _sync_hline_fractions(self, a):
        if a.band_ref is None or a.band_ref not in self.bands: return
        idx = self.bands.index(a.band_ref)
        rect = self.renderer.band_img_rect(idx, self.bands)
        if rect is None: return
        img_x, img_y, dw, dh = rect
        if dw > 0:
            a.x0_frac = (a.x0 - img_x) / float(dw)
            a.x1_frac = (a.x1 - img_x) / float(dw)
        if dh > 0:
            a.y_frac  = (a.y  - img_y) / float(dh)
    def _sync_triangle_fractions(self, tri):
        if tri.band_ref is None or tri.band_ref not in self.bands: return
        idx = self.bands.index(tri.band_ref)
        rect = self.renderer.band_img_rect(idx, self.bands)
        if rect is None: return
        img_x, img_y, dw, dh = rect
        if dw > 0:
            tri.x0_frac = (tri.x0 - img_x) / float(dw)
            tri.x1_frac = (tri.x1 - img_x) / float(dw)
        if dh > 0:
            tri.y_frac = (tri.y - img_y) / float(dh)
            tri.h_frac = tri.height / float(dh)
    def nudge_annot(self, axis, delta):
        a = self.selected_annot
        if a is None: return
        self._record_undo()
        if isinstance(a, HLine):
            if axis == "x0":   a.x0 += delta
            elif axis == "x1": a.x1 += delta
            elif axis == "y":  a.y  += delta
            self.sync_fractions_after_drag()
        elif isinstance(a, TriangleAnnot):
            if axis in ("x0", "x1"):
                a.x0 += delta;  a.x1 += delta
            elif axis == "y":
                a.y += delta
            self._sync_triangle_fractions(a)
        elif isinstance(a, FreeText):
            if axis in ("x0","x1"): a.x += delta
            elif axis == "y":       a.y += delta
        elif isinstance(a, tuple) and a[0] == "ba" and axis == "y":
            _, b, ba = a
            idx = self.bands.index(b) if b in self.bands else -1
            rect = self.renderer.band_img_rect(idx, self.bands) if idx >= 0 else None
            if rect is not None:
                img_x, img_y, dw, dh = rect
                cur_y = img_y + ba["y_frac"] * dh
                new_y = max(img_y, min(img_y + dh, cur_y + delta))
                if dh > 0:
                    ba["y_frac"] = (new_y - img_y) / float(dh)
        elif isinstance(a, tuple) and a[0] == "protein":
            _, b = a
            idx = self.bands.index(b) if b in self.bands else -1
            rect = self.renderer.band_img_rect(idx, self.bands) if idx >= 0 else None
            if rect is not None:
                img_x, img_y, dw, dh = rect
                if axis in ("x0", "x1") and dw > 0:
                    b.protein_dx_frac = getattr(b, "protein_dx_frac", 0.0) + delta / float(dw)
                elif axis == "y" and dh > 0:
                    b.protein_dy_frac = getattr(b, "protein_dy_frac", 0.0) + delta / float(dh)
        self._refresh_figure()
    def _clamp_font_size(self, size):
        return int(max(5, min(72, size)))
    def _text_selection_parts(self, a=None):
        if a is None:
            a = self.selected_annot
        if isinstance(a, FreeText):
            return ("free", None, a)
        if isinstance(a, tuple):
            if a[0] == "sl":      return ("sample", a[1], a[2])
            if a[0] == "ba":      return ("band", a[1], a[2])
            if a[0] == "kda":     return ("kda", a[1], a[2])
            if a[0] == "protein": return ("protein", a[1], a[1])
        return None
    def _is_text_selection(self, a=None):
        return self._text_selection_parts(a) is not None
    def _text_default_size(self, kind):
        return {
            "kda": FONT_KDA.getSize(),
            "sample": FONT_SAMPLE.getSize(),
            "free": FONT_ANNOT.getSize(),
            "band": FONT_BANDANN.getSize(),
            "protein": FONT_NAME.getSize(),
        }.get(kind, FONT_ANNOT.getSize())
    def _text_value(self, kind, obj):
        if kind == "free": return obj.text
        if kind == "protein": return obj.protein_name
        if kind == "kda": return kda_label_text(obj["kda"])
        return obj["text"]
    def _set_text_value(self, kind, owner, obj, value):
        if kind == "free":
            obj.text = value
        elif kind == "protein":
            obj.protein_name = value
            if owner in self.bands:
                self.list_model.set(self.bands.index(owner), value)
        elif kind in ("sample", "band"):
            obj["text"] = value
    def _text_rename_title(self, kind):
        return {
            "free": "Rename",
            "sample": "Rename label",
            "band": "Rename band annotation",
            "protein": "Rename protein",
        }.get(kind, None)
    def _text_selection_status(self, a):
        parts = self._text_selection_parts(a)
        if parts is None: return "Edit mode -- click to select"
        kind, owner, obj = parts
        txt = plain_text(self._text_value(kind, obj))
        if kind == "free":
            return "Selected: \"%s\"  |  drag / dbl-click to rename" % txt
        if kind == "sample":
            return "Selected: label \"%s\"  |  dbl-click to rename, Del to delete" % txt
        if kind == "band":
            return "Selected: band tick \"%s\"  |  drag up/down, dbl-click to rename" % txt
        if kind == "kda":
            return "Selected: kDa label \"%s\"  |  A-/A+ to resize" % txt
        return "Selected: protein name \"%s\"  |  drag/nudge, A-/A+ to resize" % txt
    def _resize_item(self, kind, obj, delta):
        if kind == "protein":
            obj.protein_size = self._clamp_font_size(
                getattr(obj, "protein_size", FONT_NAME.getSize()) + delta)
        elif kind == "free":
            obj.font_size = self._clamp_font_size(
                getattr(obj, "font_size", FONT_ANNOT.getSize()) + delta)
        else:
            base = self._text_default_size(kind)
            obj["font_size"] = self._clamp_font_size(
                obj.get("font_size", base) + delta)
    def _resize_all_text(self, delta):
        for k in self.default_font_sizes:
            self.default_font_sizes[k] = self._clamp_font_size(
                self.default_font_sizes[k] + delta)
        for b in self.bands:
            self._resize_item("protein", b, delta)
            for m in b.kda_markers:
                self._resize_item("kda", m, delta)
            for sl in b.sample_labels:
                self._resize_item("sample", sl, delta)
            for ba in b.band_annots:
                self._resize_item("band", ba, delta)
        for ft in self.freetexts:
            self._resize_item("free", ft, delta)
    def resize_text(self, delta):
        self._record_undo()
        parts = self._text_selection_parts()
        if parts is not None:
            kind, owner, obj = parts
            self._resize_item(kind, obj, delta)
            self._set_status("Resized selected text")
        else:
            self._resize_all_text(delta)
            self._set_status("Resized all text")
        self._refresh_figure()
    def copy_selected(self):
        a = self.selected_annot
        if a is None: return
        if isinstance(a, HLine):
            self.clipboard = a.shallow_copy()
            self._set_status("Copied H-Line -- Ctrl+V to paste")
        elif isinstance(a, TriangleAnnot):
            self.clipboard = a.shallow_copy()
            self._set_status("Copied triangle -- Ctrl+V to paste")
        elif isinstance(a, FreeText):
            self.clipboard = a.shallow_copy()
            self._set_status("Copied \"%s\" -- Ctrl+V to paste" % a.text)
    def paste_clipboard(self):
        if self.clipboard is None: return
        new = self.clipboard.shallow_copy()
        self._record_undo()
        if isinstance(new, HLine):
            new.x0 += PASTE_OFFSET;  new.x1 += PASTE_OFFSET;  new.y += PASTE_OFFSET
            self.hlines.append(new)
        elif isinstance(new, TriangleAnnot):
            new.x0 += PASTE_OFFSET;  new.x1 += PASTE_OFFSET;  new.y += PASTE_OFFSET
            self._sync_triangle_fractions(new)
            self.triangles.append(new)
        else:
            new.x += PASTE_OFFSET;  new.y += PASTE_OFFSET
            self.freetexts.append(new)
        self.selected_annot = new
        self._refresh_figure()
    def rename_selected(self):
        """Button-triggered rename — works for FreeText and sample labels."""
        parts = self._text_selection_parts()
        if parts is None: return
        kind, owner, obj = parts
        title = self._text_rename_title(kind)
        if title is None: return
        new_text = ask_string(title, "New text:", self._text_value(kind, obj))
        if new_text is not None:
            self._record_undo()
            self._set_text_value(kind, owner, obj, new_text)
            self._refresh_figure()
    def delete_selected_annot(self):
        a = self.selected_annot
        if a is None: return
        self._record_undo()
        if isinstance(a, HLine) and a in self.hlines:
            self.hlines.remove(a)
        elif isinstance(a, TriangleAnnot) and a in self.triangles:
            self.triangles.remove(a)
        else:
            parts = self._text_selection_parts(a)
            if parts is not None:
                kind, owner, obj = parts
                if kind == "free" and obj in self.freetexts:
                    self.freetexts.remove(obj)
                elif kind == "sample" and obj in owner.sample_labels:
                    owner.sample_labels.remove(obj)
                elif kind == "band" and obj in owner.band_annots:
                    owner.band_annots.remove(obj)
        self.selected_annot = None
        self._set_status("Edit mode -- click to select")
        self._refresh_figure()
    def _canvas_width(self):
        w = max(self.fig_scroll.getViewport().getWidth(), FIG_INIT_W)
        for i, b in enumerate(self.bands):
            rect = self.renderer.band_img_rect(i, self.bands)
            if rect is not None:
                ix, iy, dw, dh = rect
                w = max(w, ix + dw + 180)
        return w
    def _refresh_figure(self, preview_line=None, preview_triangle=None):
        hlines = list(self.hlines)
        triangles = list(self.triangles)
        if preview_line:
            x0, y, x1 = preview_line
            hlines = hlines + [HLine(x0, y, x1)]
        if preview_triangle:
            triangles = triangles + [preview_triangle]
        bi = self.renderer.render(
            self.bands, hlines, triangles, self.freetexts, self._canvas_width(),
            selected=self.selected_annot, edit_mode=self.edit_mode_active)
        self.fig_canvas.set_image(bi)
    def clear_figure(self):
        self._record_undo()
        self.bands = [];  self.hlines = [];  self.triangles = [];  self.freetexts = []
        self.sel_idx = -1;  self.selected_annot = None
        self.list_model.clear();  self._refresh_figure()
    def _choose_save_path(self, title, ext_desc, ext):
        fc = JFileChooser()
        fc.setFileFilter(FileNameExtensionFilter(ext_desc, [ext]))
        fc.setSelectedFile(JFile("figure." + ext))
        if fc.showSaveDialog(self.frame) != JFileChooser.APPROVE_OPTION:
            return None
        p = fc.getSelectedFile().getAbsolutePath()
        if not p.lower().endswith("." + ext): p += "." + ext
        return p
    def export_image(self):
        if not self.bands and not self.hlines and not self.triangles and not self.freetexts:
            JOptionPane.showMessageDialog(self.frame, "Nothing to export.",
                "Empty", JOptionPane.WARNING_MESSAGE); return
        path = self._choose_save_path("Export PNG", "PNG", "png")
        if path is None: return
        bi = self.renderer.render(self.bands, self.hlines, self.triangles, self.freetexts,
                                  self._canvas_width())
        ImageIO.write(bi, "PNG", JFile(path))
        JOptionPane.showMessageDialog(self.frame, "Saved: " + path,
            "Done", JOptionPane.INFORMATION_MESSAGE)
    def export_pdf(self):
        if not self.bands and not self.hlines and not self.triangles and not self.freetexts:
            JOptionPane.showMessageDialog(self.frame, "Nothing to export.",
                "Empty", JOptionPane.WARNING_MESSAGE); return
        dpi = ask_int("PDF resolution", "Raster DPI (72-600):", 300)
        if dpi is None: return
        dpi = max(72, min(600, dpi));  spt = 72.0 / dpi
        path = self._choose_save_path("Export PDF", "PDF", "pdf")
        if path is None: return
        from com.itextpdf.text import Rectangle as PdfRect
        cw = self._canvas_width()
        ch = self.renderer.canvas_height(self.bands, self.hlines,
                                         self.triangles, self.freetexts)
        pw = cw * spt;  ph = ch * spt
        doc    = PdfDocument(PdfRect(pw, ph), 0, 0, 0, 0)
        fos    = FileOutputStream(path)
        writer = PdfWriter.getInstance(doc, fos)
        doc.open()
        cb = writer.getDirectContent()
        try:
            g = cb.createGraphics(float(pw), float(ph))
        except:
            g = cb.createGraphicsShapes(float(pw), float(ph))
        g.scale(spt, spt)
        self.renderer.draw(g, self.bands, self.hlines, self.triangles,
                           self.freetexts, cw)
        g.dispose()
        doc.close();  fos.close()
        JOptionPane.showMessageDialog(self.frame, "PDF saved: " + path,
            "Done", JOptionPane.INFORMATION_MESSAGE)
tool = WBTool()
