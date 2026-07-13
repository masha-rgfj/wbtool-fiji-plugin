package wbtools;

import com.itextpdf.text.Document;
import com.itextpdf.text.pdf.PdfContentByte;
import com.itextpdf.text.pdf.PdfWriter;
import ij.IJ;
import ij.ImagePlus;
import ij.Prefs;
import ij.gui.ImageCanvas;
import ij.gui.Line;
import ij.gui.Overlay;
import ij.gui.Roi;
import ij.gui.TextRoi;
import ij.process.ImageConverter;
import java.awt.BasicStroke;
import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.FontMetrics;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Point;
import java.awt.Rectangle;
import java.awt.RenderingHints;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.awt.geom.AffineTransform;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.FileOutputStream;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.SwingUtilities;
import javax.swing.filechooser.FileNameExtensionFilter;
import org.scijava.command.Command;
import org.scijava.plugin.Plugin;

@Plugin(type = Command.class, menuPath = "Plugins>WB Tools>WB Tool Java 0.1.0-alpha")
public class WBToolJava implements Command {
    @Override
    public void run() {
        SwingUtilities.invokeLater(new Runnable() {
            @Override
            public void run() {
                new Controller().showFrame();
            }
        });
    }

    public static final class Controller implements ActionListener {
        private static final int TICK_LEN = 20;
        private static final int TICK_GAP = 4;
        private static final int LEFT_MARGIN = 70;
        private static final int TOP_MARGIN = 50;
        private static final int BAND_GAP = 38;
        private static final int FIG_INIT_W = 900;
        private static final int TOOL_BUTTON_W = 220;
        private static final int TOOL_BUTTON_H = 30;
        private static final String VERSION = "0.1.0-alpha";
        private static final String TITLE = "WB Tool Java " + VERSION;
        private static final Color CROP_COLOR = Color.CYAN;
        private static final float CROP_STROKE_WIDTH = 3.0f;
        private static final float SOURCE_MARKER_STROKE_WIDTH = 4.0f;
        private static final double SOURCE_MARKER_R = 10.0;
        private static final Font FONT_KDA = new Font("Arial", Font.PLAIN, 11);
        private static final Font FONT_SOURCE_KDA = new Font("Arial", Font.BOLD, 55);
        private static final Font FONT_NAME = new Font("Arial", Font.BOLD, 12);

        private JFrame frame;
        private JLabel statusLabel;
        private JButton markButton;
        private JButton cropButton;
        private JButton sourceKdaLabelsButton;
        private FigureCanvas figureCanvas;

        private ImagePlus gelImp;
        private File lastDir;
        private final List<KdaMarker> kdaMarkers = new ArrayList<KdaMarker>();
        private final List<BandCrop> bands = new ArrayList<BandCrop>();

        private boolean kdaModeActive;
        private boolean showSourceKdaLabels = true;
        private boolean waitingForCrop;
        private boolean cropWasMarking;
        private MouseListener gelMouseListener;
        private MouseListener[] savedMouseListeners = new MouseListener[0];
        private MouseMotionListener[] savedMouseMotionListeners = new MouseMotionListener[0];
        private BandCrop selectedBand;

        public void showFrame() {
            if (frame == null) {
                buildUi();
            }
            frame.setVisible(true);
            frame.toFront();
        }

        private void buildUi() {
            frame = new JFrame(TITLE);
            frame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
            frame.setLayout(new BorderLayout(8, 8));

            JPanel tools = new JPanel();
            tools.setLayout(new BoxLayout(tools, BoxLayout.Y_AXIS));
            tools.setBorder(BorderFactory.createEmptyBorder(10, 10, 10, 6));
            tools.setPreferredSize(new Dimension(TOOL_BUTTON_W + 20, 10));

            addSection(tools, "Image");
            tools.add(button("Open Image...", "open_image"));
            tools.add(Box.createVerticalStrut(8));

            addSection(tools, "kDa Markers");
            markButton = button("Mark kDa Bands", "toggle_mark_kda");
            tools.add(markButton);
            sourceKdaLabelsButton = button("Hide kDa Labels", "toggle_source_kda_labels");
            tools.add(sourceKdaLabelsButton);
            tools.add(button("Undo Last kDa", "undo_kda"));
            tools.add(button("Clear All kDa", "clear_kda"));
            tools.add(Box.createVerticalStrut(8));

            addSection(tools, "Crop");
            cropButton = button("Crop Region -> Figure", "crop");
            tools.add(cropButton);
            tools.add(Box.createVerticalStrut(8));

            addSection(tools, "Figure");
            tools.add(button("Wider", "wider"));
            tools.add(button("Narrower", "narrower"));
            tools.add(button("Clear Figure", "clear_figure"));
            tools.add(Box.createVerticalStrut(8));

            addSection(tools, "Export");
            tools.add(button("Export as PDF...", "export_pdf"));
            tools.add(Box.createVerticalGlue());

            figureCanvas = new FigureCanvas(this);
            JScrollPane scrollPane = new JScrollPane(figureCanvas);
            scrollPane.setPreferredSize(new Dimension(FIG_INIT_W, 620));

            statusLabel = new JLabel(" ");
            statusLabel.setBorder(BorderFactory.createEmptyBorder(0, 10, 8, 10));

            frame.add(tools, BorderLayout.WEST);
            frame.add(scrollPane, BorderLayout.CENTER);
            frame.add(statusLabel, BorderLayout.SOUTH);
            frame.pack();
            placeFrameLeftHalf();
        }

        private void placeFrameLeftHalf() {
            Dimension screen = Toolkit.getDefaultToolkit().getScreenSize();
            frame.setLocation(0, 0);
            frame.setSize(screen.width / 2, screen.height);
        }

        private void addSection(JPanel parent, String title) {
            JLabel label = new JLabel(title);
            label.setFont(label.getFont().deriveFont(Font.BOLD));
            label.setBorder(BorderFactory.createEmptyBorder(6, 0, 3, 0));
            parent.add(label);
        }

        private JButton button(String label, String command) {
            JButton b = new JButton(label);
            b.setActionCommand(command);
            b.addActionListener(this);
            b.setAlignmentX(JButton.LEFT_ALIGNMENT);
            Dimension size = new Dimension(TOOL_BUTTON_W, TOOL_BUTTON_H);
            b.setMinimumSize(size);
            b.setPreferredSize(size);
            b.setMaximumSize(size);
            return b;
        }

        @Override
        public void actionPerformed(ActionEvent event) {
            String command = event.getActionCommand();
            if ("open_image".equals(command)) {
                openImage();
            } else if ("toggle_mark_kda".equals(command)) {
                toggleMarkKda();
            } else if ("toggle_source_kda_labels".equals(command)) {
                toggleSourceKdaLabels();
            } else if ("undo_kda".equals(command)) {
                undoLastKda();
            } else if ("clear_kda".equals(command)) {
                clearAllKda();
            } else if ("crop".equals(command)) {
                startOrConfirmCrop();
            } else if ("wider".equals(command)) {
                resizeSelectedBand(1.12);
            } else if ("narrower".equals(command)) {
                resizeSelectedBand(1.0 / 1.12);
            } else if ("clear_figure".equals(command)) {
                clearFigure();
            } else if ("export_pdf".equals(command)) {
                exportPdf();
            }
        }

        private void openImage() {
            ImagePlus imp = openRgbImage();
            if (imp == null) {
                return;
            }
            cancelCropMode();
            if (kdaModeActive) {
                deactivateKdaMode();
            }
            gelImp = imp;
            kdaMarkers.clear();
            showImageRightHalf(imp);
            IJ.setTool("rectangle");
            setStatus("Image loaded. Mark kDa bands or draw a crop.");
        }

        private void cancelCropMode() {
            waitingForCrop = false;
            cropWasMarking = false;
            if (cropButton != null) {
                cropButton.setText("Crop Region -> Figure");
                cropButton.setBackground(null);
            }
        }

        private ImagePlus openRgbImage() {
            JFileChooser chooser = new JFileChooser();
            chooser.setFileFilter(new FileNameExtensionFilter(
                    "Image files (TIFF, PNG, JPEG)", "tif", "tiff", "png", "jpg", "jpeg"));
            if (lastDir != null) {
                chooser.setCurrentDirectory(lastDir);
            } else {
                String prefDir = Prefs.get("wbtool.last_dir", null);
                if (prefDir != null) {
                    chooser.setCurrentDirectory(new File(prefDir));
                }
            }
            if (chooser.showOpenDialog(frame) != JFileChooser.APPROVE_OPTION) {
                return null;
            }
            File chosen = chooser.getSelectedFile();
            lastDir = chosen.getParentFile();
            if (lastDir != null) {
                Prefs.set("wbtool.last_dir", lastDir.getAbsolutePath());
            }
            ImagePlus imp = IJ.openImage(chosen.getAbsolutePath());
            if (imp == null) {
                JOptionPane.showMessageDialog(frame, "Could not open: " + chosen.getAbsolutePath(),
                        "Open image", JOptionPane.ERROR_MESSAGE);
                return null;
            }
            if (imp.getType() != ImagePlus.COLOR_RGB) {
                new ImageConverter(imp).convertToRGB();
            }
            return imp;
        }

        private void showImageRightHalf(ImagePlus imp) {
            imp.show();
            Dimension screen = Toolkit.getDefaultToolkit().getScreenSize();
            if (imp.getWindow() != null) {
                imp.getWindow().setLocation(screen.width / 2, 0);
                imp.getWindow().setSize(screen.width / 2, screen.height);
            }
        }

        private void toggleMarkKda() {
            if (gelImp == null) {
                JOptionPane.showMessageDialog(frame, "Open a gel image first.",
                        "No image", JOptionPane.WARNING_MESSAGE);
                return;
            }
            if (kdaModeActive) {
                deactivateKdaMode();
            } else {
                activateKdaMode();
            }
        }

        private void activateKdaMode() {
            if (gelImp == null || gelImp.getCanvas() == null) {
                return;
            }
            kdaModeActive = true;
            markButton.setText("Stop Marking kDa");
            markButton.setBackground(new Color(255, 180, 0));
            setStatus("kDa marking active. Click a marker band in the source image.");
            IJ.setTool("point");

            final ImageCanvas canvas = gelImp.getCanvas();
            savedMouseListeners = canvas.getMouseListeners();
            for (MouseListener listener : savedMouseListeners) {
                canvas.removeMouseListener(listener);
            }
            savedMouseMotionListeners = canvas.getMouseMotionListeners();
            for (MouseMotionListener listener : savedMouseMotionListeners) {
                canvas.removeMouseMotionListener(listener);
            }

            gelMouseListener = new MouseAdapter() {
                @Override
                public void mousePressed(MouseEvent event) {
                    if (!kdaModeActive || event.getButton() != MouseEvent.BUTTON1) {
                        return;
                    }
                    event.consume();
                    double x = canvas.offScreenXD(event.getX());
                    double y = canvas.offScreenYD(event.getY());
                    onGelClick(x, y);
                }
            };
            canvas.addMouseListener(gelMouseListener);
        }

        private void deactivateKdaMode() {
            kdaModeActive = false;
            markButton.setText("Mark kDa Bands");
            markButton.setBackground(null);
            if (gelImp != null && gelImp.getCanvas() != null) {
                ImageCanvas canvas = gelImp.getCanvas();
                if (gelMouseListener != null) {
                    canvas.removeMouseListener(gelMouseListener);
                }
                for (MouseListener listener : savedMouseListeners) {
                    canvas.addMouseListener(listener);
                }
                for (MouseMotionListener listener : savedMouseMotionListeners) {
                    canvas.addMouseMotionListener(listener);
                }
            }
            gelMouseListener = null;
            savedMouseListeners = new MouseListener[0];
            savedMouseMotionListeners = new MouseMotionListener[0];
            IJ.setTool("rectangle");
            setStatus(" ");
        }

        private void onGelClick(double x, double y) {
            String value = JOptionPane.showInputDialog(frame,
                    "Enter kDa label for this band:", "0");
            if (value == null) {
                return;
            }
            value = value.trim();
            if (value.length() == 0) {
                JOptionPane.showMessageDialog(frame, "Please enter a kDa label.",
                        "Invalid kDa", JOptionPane.WARNING_MESSAGE);
                return;
            }
            kdaMarkers.add(new KdaMarker(x, y, value));
            Collections.sort(kdaMarkers, new Comparator<KdaMarker>() {
                @Override
                public int compare(KdaMarker a, KdaMarker b) {
                    return Double.compare(a.yAbs, b.yAbs);
                }
            });
            redrawKdaOverlay();
            setStatus("kDa marking active. " + kdaMarkers.size() + " marker(s) saved.");
        }

        private void toggleSourceKdaLabels() {
            showSourceKdaLabels = !showSourceKdaLabels;
            sourceKdaLabelsButton.setText(showSourceKdaLabels ? "Hide kDa Labels" : "Show kDa Labels");
            redrawKdaOverlay();
            setStatus(showSourceKdaLabels
                    ? "kDa labels are visible on the source image."
                    : "kDa labels are hidden on the source image; marker Xs remain visible.");
        }

        private void redrawKdaOverlay() {
            if (gelImp == null) {
                return;
            }
            if (kdaMarkers.isEmpty()) {
                gelImp.setOverlay(null);
                gelImp.updateAndDraw();
                return;
            }
            Overlay overlay = new Overlay();
            for (KdaMarker marker : kdaMarkers) {
                double x = marker.xAbs;
                double y = marker.yAbs;
                Line diagA = new Line(x - SOURCE_MARKER_R, y - SOURCE_MARKER_R,
                        x + SOURCE_MARKER_R, y + SOURCE_MARKER_R);
                diagA.setStrokeColor(Color.RED);
                diagA.setStrokeWidth(SOURCE_MARKER_STROKE_WIDTH);
                overlay.add(diagA);
                Line diagB = new Line(x - SOURCE_MARKER_R, y + SOURCE_MARKER_R,
                        x + SOURCE_MARKER_R, y - SOURCE_MARKER_R);
                diagB.setStrokeColor(Color.RED);
                diagB.setStrokeWidth(SOURCE_MARKER_STROKE_WIDTH);
                overlay.add(diagB);
                if (showSourceKdaLabels) {
                    TextRoi label = new TextRoi(x + 14.0, y - 52.0, marker.label, FONT_SOURCE_KDA);
                    label.setStrokeColor(Color.RED);
                    label.setFillColor(new Color(255, 255, 255, 170));
                    overlay.add(label);
                }
            }
            gelImp.setOverlay(overlay);
            gelImp.updateAndDraw();
        }

        private void undoLastKda() {
            if (!kdaMarkers.isEmpty()) {
                kdaMarkers.remove(kdaMarkers.size() - 1);
                redrawKdaOverlay();
            }
        }

        private void clearAllKda() {
            kdaMarkers.clear();
            redrawKdaOverlay();
            if (kdaModeActive) {
                setStatus("kDa marking active. Click a marker band in the source image.");
            }
        }

        private void startOrConfirmCrop() {
            if (gelImp == null) {
                JOptionPane.showMessageDialog(frame, "Open a gel image first.",
                        "No image", JOptionPane.WARNING_MESSAGE);
                return;
            }
            if (!waitingForCrop) {
                waitingForCrop = true;
                cropWasMarking = kdaModeActive;
                if (kdaModeActive) {
                    deactivateKdaMode();
                }
                setCropSelectionTool();
                cropButton.setText("Confirm Crop");
                cropButton.setBackground(new Color(255, 180, 0));
                setStatus("Draw a crop on the source image. You can rotate it, then click Confirm Crop.");
                return;
            }

            Roi roi = gelImp.getRoi();
            if (roi == null) {
                JOptionPane.showMessageDialog(frame, "No selection found. Click Crop again and draw first.",
                        "No selection", JOptionPane.WARNING_MESSAGE);
                setCropSelectionTool();
                setStatus("Crop mode is still active. Draw a crop on the source image, then click Confirm Crop.");
                return;
            }
            styleCropRoi(roi);
            CropResult crop = rotatedCropFromRoi(gelImp, roi);
            if (crop == null) {
                JOptionPane.showMessageDialog(frame, "Selection is too small. Please try again.",
                        "Crop", JOptionPane.WARNING_MESSAGE);
                setCropSelectionTool();
                setStatus("Crop mode is still active. Draw a larger crop, then click Confirm Crop.");
                return;
            }
            waitingForCrop = false;
            cropButton.setText("Crop Region -> Figure");
            cropButton.setBackground(null);

            List<CropMarker> localMarkers = new ArrayList<CropMarker>();
            for (KdaMarker marker : kdaMarkers) {
                double yInCrop = markerYInCrop(marker, crop.x, crop.y, crop.angleDeg);
                if (yInCrop >= -0.5 && yInCrop <= crop.height + 0.5) {
                    localMarkers.add(new CropMarker(marker.label, yInCrop, marker.xAbs, marker.yAbs));
                }
            }
            Collections.sort(localMarkers, new Comparator<CropMarker>() {
                @Override
                public int compare(CropMarker a, CropMarker b) {
                    return Double.compare(a.yInCrop, b.yInCrop);
                }
            });

            String name = JOptionPane.showInputDialog(frame, "Enter crop label:", "Protein");
            if (name == null) {
                restoreCropMarkMode();
                return;
            }
            if (name.trim().length() == 0) {
                name = "Protein";
            }

            BufferedImage image = crop.imagePlus.getProcessor().convertToRGB().getBufferedImage();
            int displayWidth = chooseInitialDisplayWidth(image.getWidth());
            BandCrop band = new BandCrop(image, localMarkers, name.trim(), displayWidth);
            band.cropX = crop.x;
            band.cropY = crop.y;
            band.cropWidth = crop.width;
            band.cropHeight = crop.height;
            band.cropAngleDeg = crop.angleDeg;
            bands.add(band);
            selectedBand = band;
            figureCanvas.refreshLayout();
            setStatus("Crop added. kDa ticks are tied to the crop and scale with it.");
            restoreCropMarkMode();
        }

        private void restoreCropMarkMode() {
            if (cropWasMarking) {
                activateKdaMode();
            }
        }

        private int chooseInitialDisplayWidth(int imageWidth) {
            if (!bands.isEmpty()) {
                return bands.get(bands.size() - 1).displayWidth;
            }
            int available = Math.max(220, figureCanvas.getWidth() - 180);
            if (available <= 220) {
                available = 650;
            }
            return Math.max(80, Math.min(imageWidth, available));
        }

        private void setCropSelectionTool() {
            Roi.setColor(CROP_COLOR);
            trySetDefaultRoiStrokeWidth(CROP_STROKE_WIDTH);
            try {
                IJ.setTool("rotated rectangle");
            } catch (RuntimeException ex) {
                IJ.setTool("rectangle");
            }
        }

        private void trySetDefaultRoiStrokeWidth(float width) {
            try {
                Method method = Roi.class.getMethod("setDefaultStrokeWidth", double.class);
                method.invoke(null, Double.valueOf(width));
            } catch (Throwable ignored) {
                // Older ImageJ builds do not expose a global default stroke width.
            }
        }

        private void styleCropRoi(Roi roi) {
            roi.setStrokeColor(CROP_COLOR);
            roi.setStrokeWidth(CROP_STROKE_WIDTH);
            gelImp.updateAndDraw();
        }

        private CropResult rotatedCropFromRoi(ImagePlus imp, Roi roi) {
            Rectangle bounds = roi.getBounds();
            double x = bounds.x;
            double y = bounds.y;
            int width = bounds.width;
            int height = bounds.height;
            double angle = 0.0;

            try {
                ij.process.FloatPolygon polygon = roi.getFloatPolygon();
                if (polygon != null && polygon.npoints >= 4) {
                    double x0 = polygon.xpoints[0];
                    double y0 = polygon.ypoints[0];
                    double x1 = polygon.xpoints[1];
                    double y1 = polygon.ypoints[1];
                    double x2 = polygon.xpoints[2];
                    double y2 = polygon.ypoints[2];
                    double sideW = distance(x0, y0, x1, y1);
                    double sideH = distance(x1, y1, x2, y2);
                    if (sideW >= 2.0 && sideH >= 2.0) {
                        x = x0;
                        y = y0;
                        width = (int) Math.round(sideW);
                        height = (int) Math.round(sideH);
                        angle = Math.atan2(y1 - y0, x1 - x0);
                    }
                }
            } catch (RuntimeException ignored) {
                // Fall back to the ordinary rectangular ROI bounds.
            }

            if (width < 2 || height < 2) {
                return null;
            }

            ImagePlus cropped;
            if (Math.abs(angle) < 0.0001) {
                Roi oldRoi = imp.getRoi();
                imp.setRoi((int) Math.round(x), (int) Math.round(y), width, height);
                cropped = imp.crop();
                imp.setRoi(oldRoi);
                return new CropResult(cropped, x, y, width, height, 0.0);
            }

            BufferedImage src = imp.getProcessor().convertToRGB().getBufferedImage();
            BufferedImage out = new BufferedImage(width, height, BufferedImage.TYPE_INT_RGB);
            Graphics2D g = out.createGraphics();
            g.setRenderingHint(RenderingHints.KEY_INTERPOLATION,
                    RenderingHints.VALUE_INTERPOLATION_BICUBIC);
            g.setColor(Color.WHITE);
            g.fillRect(0, 0, out.getWidth(), out.getHeight());

            double c = Math.cos(angle);
            double s = Math.sin(angle);
            double tx = -(c * x + s * y);
            double ty = (s * x - c * y);
            AffineTransform transform = new AffineTransform(c, -s, s, c, tx, ty);
            g.drawImage(src, transform, null);
            g.dispose();
            cropped = new ImagePlus("Rotated crop", out);
            return new CropResult(cropped, x, y, width, height, Math.toDegrees(angle));
        }

        private static double markerYInCrop(KdaMarker marker, double cropX, double cropY,
                double cropAngleDeg) {
            double angle = Math.toRadians(cropAngleDeg);
            double dx = marker.xAbs - cropX;
            double dy = marker.yAbs - cropY;
            return -Math.sin(angle) * dx + Math.cos(angle) * dy;
        }

        private static double distance(double ax, double ay, double bx, double by) {
            double dx = ax - bx;
            double dy = ay - by;
            return Math.sqrt(dx * dx + dy * dy);
        }

        private void resizeSelectedBand(double factor) {
            BandCrop band = selectedBand;
            if (band == null && !bands.isEmpty()) {
                band = bands.get(bands.size() - 1);
                selectedBand = band;
            }
            if (band == null) {
                return;
            }
            int next = (int) Math.round(band.displayWidth * factor);
            band.displayWidth = Math.max(50, Math.min(next, band.image.getWidth() * 5));
            figureCanvas.refreshLayout();
            setStatus("Crop resized. kDa ticks were recomputed from the crop scale.");
        }

        private void clearFigure() {
            bands.clear();
            selectedBand = null;
            figureCanvas.refreshLayout();
        }

        private void exportPdf() {
            if (bands.isEmpty()) {
                JOptionPane.showMessageDialog(frame, "Nothing to export.",
                        "Export PDF", JOptionPane.WARNING_MESSAGE);
                return;
            }
            String dpiText = JOptionPane.showInputDialog(frame, "Raster DPI for crop images:", "300");
            if (dpiText == null) {
                return;
            }
            int dpi;
            try {
                dpi = Integer.parseInt(dpiText.trim());
            } catch (NumberFormatException ex) {
                dpi = 300;
            }
            dpi = Math.max(72, Math.min(600, dpi));
            File path = chooseSavePath("Export PDF", "PDF", "pdf");
            if (path == null) {
                return;
            }

            Dimension size = figureCanvas.contentSize();
            double scaleToPoints = 72.0 / dpi;
            float pageWidth = (float) (size.width * scaleToPoints);
            float pageHeight = (float) (size.height * scaleToPoints);

            FileOutputStream out = null;
            Document doc = null;
            try {
                out = new FileOutputStream(path);
                doc = new Document(new com.itextpdf.text.Rectangle(pageWidth, pageHeight), 0, 0, 0, 0);
                PdfWriter writer = PdfWriter.getInstance(doc, out);
                doc.open();
                PdfContentByte cb = writer.getDirectContent();
                Graphics2D g = cb.createGraphics(pageWidth, pageHeight);
                g.scale(scaleToPoints, scaleToPoints);
                figureCanvas.renderFigure(g, false);
                g.dispose();
                doc.close();
                out.close();
                JOptionPane.showMessageDialog(frame, "PDF saved: " + path.getAbsolutePath(),
                        "Export PDF", JOptionPane.INFORMATION_MESSAGE);
            } catch (Throwable ex) {
                try {
                    if (doc != null && doc.isOpen()) {
                        doc.close();
                    }
                    if (out != null) {
                        out.close();
                    }
                } catch (Exception ignored) {
                    // Ignore cleanup failures and show the original export problem.
                }
                JOptionPane.showMessageDialog(frame,
                        "PDF export failed. Make sure the iText module/JAR is available in Fiji.\n"
                                + ex.getClass().getSimpleName() + ": " + ex.getMessage(),
                        "Export PDF", JOptionPane.ERROR_MESSAGE);
            }
        }

        private File chooseSavePath(String title, String description, String extension) {
            JFileChooser chooser = new JFileChooser();
            chooser.setDialogTitle(title);
            chooser.setFileFilter(new FileNameExtensionFilter(description, extension));
            if (lastDir != null) {
                chooser.setCurrentDirectory(lastDir);
            }
            if (chooser.showSaveDialog(frame) != JFileChooser.APPROVE_OPTION) {
                return null;
            }
            File file = chooser.getSelectedFile();
            if (!file.getName().toLowerCase().endsWith("." + extension)) {
                file = new File(file.getParentFile(), file.getName() + "." + extension);
            }
            return file;
        }

        private void setStatus(String text) {
            statusLabel.setText(text == null ? " " : text);
        }

        private List<BandCrop> bands() {
            return bands;
        }

        private BandCrop selectedBand() {
            return selectedBand;
        }

        private void selectBand(BandCrop band) {
            selectedBand = band;
            figureCanvas.repaint();
        }
    }

    private static final class FigureCanvas extends JPanel {
        private final Controller controller;
        private Point dragLast;
        private BandCrop dragBand;

        FigureCanvas(final Controller controller) {
            this.controller = controller;
            setBackground(Color.WHITE);
            setPreferredSize(new Dimension(Controller.FIG_INIT_W, 300));

            MouseAdapter mouse = new MouseAdapter() {
                @Override
                public void mousePressed(MouseEvent event) {
                    requestFocusInWindow();
                    BandCrop band = bandAt(event.getX(), event.getY());
                    controller.selectBand(band);
                    if (band != null) {
                        dragBand = band;
                        dragLast = event.getPoint();
                    }
                }

                @Override
                public void mouseDragged(MouseEvent event) {
                    if (dragBand == null || dragLast == null) {
                        return;
                    }
                    int dx = event.getX() - dragLast.x;
                    int dy = event.getY() - dragLast.y;
                    dragBand.yOffset += dy;
                    dragLast = event.getPoint();
                    refreshLayout();
                }

                @Override
                public void mouseReleased(MouseEvent event) {
                    dragBand = null;
                    dragLast = null;
                }
            };
            addMouseListener(mouse);
            addMouseMotionListener(mouse);
        }

        void refreshLayout() {
            setPreferredSize(contentSize());
            revalidate();
            repaint();
        }

        Dimension contentSize() {
            int width = Controller.FIG_INIT_W;
            int y = Controller.TOP_MARGIN;
            for (BandCrop band : controller.bands()) {
                Rectangle rect = layoutRectFor(band, y);
                width = Math.max(width, rect.x + rect.width + Controller.TICK_LEN + 100);
                y += rect.height + Controller.BAND_GAP + 20;
            }
            return new Dimension(width, Math.max(300, y + 20));
        }

        private Rectangle layoutRectFor(BandCrop band, int baseY) {
            int h = band.displayHeight();
            int x = Controller.LEFT_MARGIN + (int) Math.round(band.xOffset);
            int y = baseY + (int) Math.round(band.yOffset);
            return new Rectangle(x, y, band.displayWidth, h);
        }

        private BandCrop bandAt(int x, int y) {
            int baseY = Controller.TOP_MARGIN;
            for (BandCrop band : controller.bands()) {
                Rectangle rect = layoutRectFor(band, baseY);
                if (rect.contains(x, y)) {
                    return band;
                }
                baseY += rect.height + Controller.BAND_GAP + 20;
            }
            return null;
        }

        @Override
        protected void paintComponent(Graphics graphics) {
            super.paintComponent(graphics);
            Graphics2D g = (Graphics2D) graphics.create();
            renderFigure(g, true);
            g.dispose();
        }

        void renderFigure(Graphics2D g, boolean paintBackground) {
            Dimension size = contentSize();
            g.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
                    RenderingHints.VALUE_ANTIALIAS_ON);
            g.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING,
                    RenderingHints.VALUE_TEXT_ANTIALIAS_ON);
            if (paintBackground) {
                g.setColor(Color.WHITE);
                g.fillRect(0, 0, size.width, size.height);
            }
            if (controller.bands().isEmpty()) {
                if (paintBackground) {
                    g.setColor(Color.GRAY);
                    g.setFont(new Font("Arial", Font.ITALIC, 14));
                    g.drawString("No crops yet", 40, 150);
                }
                return;
            }

            int baseY = Controller.TOP_MARGIN;
            for (BandCrop band : controller.bands()) {
                Rectangle rect = layoutRectFor(band, baseY);
                drawBand(g, band, rect, band == controller.selectedBand());
                baseY += rect.height + Controller.BAND_GAP + 20;
            }
        }

        private void drawBand(Graphics2D g, BandCrop band, Rectangle rect, boolean selected) {
            g.drawImage(band.image, rect.x, rect.y, rect.width, rect.height, null);

            g.setColor(selected ? Controller.CROP_COLOR : Color.BLACK);
            g.setStroke(new BasicStroke(selected ? 2.0f : 1.2f));
            g.drawRect(rect.x, rect.y, rect.width, rect.height);

            double scale = band.scale();
            g.setFont(Controller.FONT_KDA);
            FontMetrics fm = g.getFontMetrics();
            g.setColor(Color.BLACK);
            g.setStroke(new BasicStroke(1.2f));
            for (CropMarker marker : band.markers) {
                int ty = rect.y + (int) Math.round(marker.yInCrop * scale);
                int x1 = rect.x - 2;
                int x0 = x1 - Controller.TICK_LEN;
                g.drawLine(x0, ty, x1, ty);
                int baseline = ty + (fm.getAscent() - fm.getDescent()) / 2;
                int labelWidth = fm.stringWidth(marker.label);
                g.drawString(marker.label, x0 - Controller.TICK_GAP - labelWidth, baseline);
            }

            if (band.label != null && band.label.length() > 0) {
                g.setFont(Controller.FONT_NAME);
                FontMetrics nameMetrics = g.getFontMetrics();
                int textWidth = nameMetrics.stringWidth(band.label);
                int x = rect.x + rect.width / 2 - textWidth / 2;
                int y = rect.y + rect.height + nameMetrics.getAscent() + 5;
                g.drawString(band.label, x, y);
            }
        }
    }

    private static final class KdaMarker {
        final double xAbs;
        final double yAbs;
        final String label;

        KdaMarker(double xAbs, double yAbs, String label) {
            this.xAbs = xAbs;
            this.yAbs = yAbs;
            this.label = label;
        }
    }

    private static final class CropMarker {
        final String label;
        final double yInCrop;
        final double xAbs;
        final double yAbs;

        CropMarker(String label, double yInCrop, double xAbs, double yAbs) {
            this.label = label;
            this.yInCrop = yInCrop;
            this.xAbs = xAbs;
            this.yAbs = yAbs;
        }
    }

    private static final class BandCrop {
        final BufferedImage image;
        final List<CropMarker> markers;
        final String label;
        int displayWidth;
        double xOffset;
        double yOffset;
        double cropX;
        double cropY;
        int cropWidth;
        int cropHeight;
        double cropAngleDeg;

        BandCrop(BufferedImage image, List<CropMarker> markers, String label, int displayWidth) {
            this.image = image;
            this.markers = markers;
            this.label = label;
            this.displayWidth = displayWidth;
        }

        double scale() {
            return displayWidth / (double) image.getWidth();
        }

        int displayHeight() {
            return Math.max(1, (int) Math.round(image.getHeight() * scale()));
        }
    }

    private static final class CropResult {
        final ImagePlus imagePlus;
        final double x;
        final double y;
        final int width;
        final int height;
        final double angleDeg;

        CropResult(ImagePlus imagePlus, double x, double y, int width, int height, double angleDeg) {
            this.imagePlus = imagePlus;
            this.x = x;
            this.y = y;
            this.width = width;
            this.height = height;
            this.angleDeg = angleDeg;
        }
    }
}
