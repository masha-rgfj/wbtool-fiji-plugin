package wbtools;

import com.itextpdf.text.Document;
import com.itextpdf.text.pdf.PdfContentByte;
import com.itextpdf.text.pdf.PdfWriter;
import ij.IJ;
import ij.ImagePlus;
import ij.Prefs;
import ij.WindowManager;
import ij.gui.ImageCanvas;
import ij.gui.Line;
import ij.gui.Overlay;
import ij.gui.Roi;
import ij.gui.TextRoi;
import ij.gui.Toolbar;
import ij.process.ImageConverter;
import java.awt.BasicStroke;
import java.awt.BorderLayout;
import java.awt.CardLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.FontMetrics;
import java.awt.GridLayout;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Point;
import java.awt.Rectangle;
import java.awt.RenderingHints;
import java.awt.Toolkit;
import java.awt.datatransfer.StringSelection;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.FocusAdapter;
import java.awt.event.FocusEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.geom.AffineTransform;
import java.awt.image.BufferedImage;
import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.lang.reflect.Method;
import java.nio.file.Files;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.List;
import java.util.Locale;
import java.util.Properties;
import java.util.UUID;
import javax.imageio.ImageIO;
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
import javax.swing.JTable;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.ListSelectionModel;
import javax.swing.filechooser.FileNameExtensionFilter;
import javax.swing.table.DefaultTableModel;
import org.scijava.command.Command;
import org.scijava.plugin.Plugin;

@Plugin(type = Command.class, menuPath = "Plugins>WB Tools>WB Tool Java 0.4.0-alpha")
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
        private static final String VERSION = "0.4.0-alpha";
        private static final String TITLE = "WB Tool Java " + VERSION;
        private static final Color CROP_COLOR = Color.CYAN;
        private static final float CROP_STROKE_WIDTH = 3.0f;
        private static final float SOURCE_MARKER_STROKE_WIDTH = 4.0f;
        private static final double SOURCE_MARKER_R = 10.0;
        private static final Font FONT_KDA = new Font("Arial", Font.PLAIN, 11);
        private static final Font FONT_SOURCE_KDA = new Font("Arial", Font.BOLD, 55);
        private static final Font FONT_NAME = new Font("Arial", Font.BOLD, 12);
        private static final String CARD_HOME = "home";
        private static final String CARD_EDITOR = "editor";

        private JFrame frame;
        private JLabel statusLabel;
        private JButton markButton;
        private JButton cropButton;
        private JButton sourceKdaLabelsButton;
        private FigureCanvas figureCanvas;
        private CardLayout cards;
        private JPanel cardPanel;
        private DefaultTableModel historyModel;
        private JTable historyTable;
        private JTextField figureTitleField;

        private ImagePlus gelImp;
        private ImagePlus markerImp;
        private File lastDir;
        private String gelImagePath = "";
        private String markerImagePath = "";
        private String openedImagePath = "";
        private String projectId;
        private long projectCreatedAt;
        private final List<KdaMarker> kdaMarkers = new ArrayList<KdaMarker>();
        private final List<BandCrop> bands = new ArrayList<BandCrop>();
        private final List<FigureRecord> historyRecords = new ArrayList<FigureRecord>();

        private boolean kdaModeActive;
        private boolean showSourceKdaLabels = true;
        private boolean waitingForCrop;
        private boolean cropWasMarking;
        private MouseListener gelMouseListener;
        private ImageCanvas kdaCanvas;
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

            cards = new CardLayout();
            cardPanel = new JPanel(cards);
            cardPanel.add(buildHomePanel(), CARD_HOME);
            cardPanel.add(buildEditorPanel(), CARD_EDITOR);

            statusLabel = new JLabel(" ");
            statusLabel.setBorder(BorderFactory.createEmptyBorder(0, 10, 8, 10));

            frame.add(cardPanel, BorderLayout.CENTER);
            frame.add(statusLabel, BorderLayout.SOUTH);
            frame.addWindowListener(new WindowAdapter() {
                @Override
                public void windowClosing(WindowEvent event) {
                    saveProject(false);
                }
            });
            frame.pack();
            placeFrameLeftHalf();
            showHome();
        }

        private JPanel buildHomePanel() {
            JPanel home = new JPanel(new BorderLayout(12, 12));
            home.setBorder(BorderFactory.createEmptyBorder(24, 28, 24, 28));

            JPanel heading = new JPanel();
            heading.setLayout(new BoxLayout(heading, BoxLayout.Y_AXIS));
            JLabel title = new JLabel("GelAnno");
            title.setFont(title.getFont().deriveFont(Font.BOLD, 28.0f));
            JLabel subtitle = new JLabel("Recent figures and coordinate logs");
            subtitle.setForeground(Color.DARK_GRAY);
            heading.add(title);
            heading.add(Box.createVerticalStrut(4));
            heading.add(subtitle);

            JButton blank = new JButton("+  Blank figure");
            blank.setActionCommand("new_figure");
            blank.addActionListener(this);
            blank.setPreferredSize(new Dimension(180, 70));
            heading.add(Box.createVerticalStrut(18));
            heading.add(blank);
            home.add(heading, BorderLayout.NORTH);

            historyModel = new DefaultTableModel(
                    new Object[] {"Name", "Last modified", "Crops"}, 0) {
                @Override
                public boolean isCellEditable(int row, int column) {
                    return false;
                }
            };
            historyTable = new JTable(historyModel);
            historyTable.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
            historyTable.setRowHeight(30);
            historyTable.getColumnModel().getColumn(0).setPreferredWidth(390);
            historyTable.getColumnModel().getColumn(1).setPreferredWidth(170);
            historyTable.getColumnModel().getColumn(2).setPreferredWidth(60);
            historyTable.addMouseListener(new MouseAdapter() {
                @Override
                public void mouseClicked(MouseEvent event) {
                    if (event.getClickCount() == 2) {
                        openSelectedHistoryFigure();
                    }
                }
            });
            JScrollPane recent = new JScrollPane(historyTable);
            recent.setBorder(BorderFactory.createTitledBorder("Recent figures"));
            home.add(recent, BorderLayout.CENTER);

            JPanel actions = new JPanel();
            actions.add(homeButton("Open / Edit", "open_history"));
            actions.add(homeButton("View Coordinate Log", "view_log"));
            actions.add(homeButton("Copy Coordinates", "copy_log"));
            actions.add(homeButton("Delete", "delete_history"));
            actions.add(homeButton("Refresh", "refresh_history"));
            home.add(actions, BorderLayout.SOUTH);
            return home;
        }

        private JButton homeButton(String label, String command) {
            JButton button = new JButton(label);
            button.setActionCommand(command);
            button.addActionListener(this);
            return button;
        }

        private JPanel buildEditorPanel() {
            JPanel editor = new JPanel(new BorderLayout(8, 8));

            JPanel tools = new JPanel();
            tools.setLayout(new BoxLayout(tools, BoxLayout.Y_AXIS));
            tools.setBorder(BorderFactory.createEmptyBorder(10, 10, 10, 6));
            tools.setPreferredSize(new Dimension(TOOL_BUTTON_W + 20, 10));

            addSection(tools, "GelAnno");
            tools.add(button("Back to Home", "home"));
            tools.add(button("New Figure", "new_figure"));
            tools.add(Box.createVerticalStrut(8));

            addSection(tools, "Image");
            tools.add(button("Open Gel Image...", "open_image"));
            tools.add(Box.createVerticalStrut(8));

            addSection(tools, "kDa Markers");
            tools.add(button("Open kDa Marker Image...", "open_marker_image"));
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
            tools.add(button("Edit Selected Coordinates...", "edit_coordinates"));
            tools.add(button("View Coordinate Log", "view_current_log"));
            tools.add(button("Copy Coordinate Log", "copy_current_log"));
            tools.add(button("Clear Figure", "clear_figure"));
            tools.add(Box.createVerticalStrut(8));

            addSection(tools, "Export");
            tools.add(button("Export as PDF...", "export_pdf"));
            tools.add(Box.createVerticalGlue());

            figureCanvas = new FigureCanvas(this);
            JScrollPane scrollPane = new JScrollPane(figureCanvas);
            scrollPane.setPreferredSize(new Dimension(FIG_INIT_W, 620));

            JPanel titleBar = new JPanel(new BorderLayout(8, 0));
            titleBar.setBorder(BorderFactory.createEmptyBorder(10, 10, 0, 10));
            titleBar.add(new JLabel("Figure name:"), BorderLayout.WEST);
            figureTitleField = new JTextField("Untitled figure");
            figureTitleField.addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent event) {
                    saveProject(true);
                }
            });
            figureTitleField.addFocusListener(new FocusAdapter() {
                @Override
                public void focusLost(FocusEvent event) {
                    saveProject(false);
                }
            });
            titleBar.add(figureTitleField, BorderLayout.CENTER);

            editor.add(titleBar, BorderLayout.NORTH);
            editor.add(tools, BorderLayout.WEST);
            editor.add(scrollPane, BorderLayout.CENTER);
            return editor;
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
            if ("new_figure".equals(command)) {
                newFigure();
            } else if ("home".equals(command)) {
                saveProject(false);
                showHome();
            } else if ("open_history".equals(command)) {
                openSelectedHistoryFigure();
            } else if ("view_log".equals(command)) {
                viewSelectedHistoryLog();
            } else if ("copy_log".equals(command)) {
                copySelectedHistoryLog();
            } else if ("delete_history".equals(command)) {
                deleteSelectedHistoryFigure();
            } else if ("refresh_history".equals(command)) {
                refreshHistory();
            } else if ("open_image".equals(command)) {
                openImage();
            } else if ("open_marker_image".equals(command)) {
                openMarkerImage();
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
            } else if ("edit_coordinates".equals(command)) {
                editSelectedCoordinates();
            } else if ("view_current_log".equals(command)) {
                showCoordinateLog(coordinateLog(), figureTitle() + " - Coordinate Log");
            } else if ("copy_current_log".equals(command)) {
                copyText(coordinateLog(), "Coordinate log copied to the clipboard.");
            } else if ("clear_figure".equals(command)) {
                clearFigure();
            } else if ("export_pdf".equals(command)) {
                exportPdf();
            }
        }

        private void newFigure() {
            saveProject(false);
            cancelCropMode();
            if (kdaModeActive) {
                deactivateKdaMode();
            }
            bands.clear();
            kdaMarkers.clear();
            selectedBand = null;
            gelImp = null;
            markerImp = null;
            gelImagePath = "";
            markerImagePath = "";
            projectId = UUID.randomUUID().toString();
            projectCreatedAt = System.currentTimeMillis();
            figureTitleField.setText("Untitled figure");
            figureCanvas.refreshLayout();
            cards.show(cardPanel, CARD_EDITOR);
            frame.setTitle("GelAnno - Untitled figure");
            saveProject(false);
            setStatus("New figure created. Changes are saved automatically.");
        }

        private void showHome() {
            refreshHistory();
            cards.show(cardPanel, CARD_HOME);
            frame.setTitle("GelAnno");
            setStatus("Select a recent figure, or create a blank figure.");
        }

        private File historyRoot() {
            String configured = Prefs.get("gelanno.history_dir", null);
            File root;
            if (configured != null && configured.trim().length() > 0) {
                root = new File(configured);
            } else {
                String preferences = IJ.getDirectory("preferences");
                if (preferences == null) {
                    preferences = System.getProperty("user.home", ".");
                }
                root = new File(preferences, "GelAnno/figure-history");
                Prefs.set("gelanno.history_dir", root.getAbsolutePath());
            }
            if (!root.exists()) {
                root.mkdirs();
            }
            return root;
        }

        private void refreshHistory() {
            if (historyModel == null) {
                return;
            }
            historyRecords.clear();
            File[] directories = historyRoot().listFiles();
            if (directories != null) {
                for (File directory : directories) {
                    if (!directory.isDirectory()) {
                        continue;
                    }
                    Properties properties = readProperties(new File(directory, "project.properties"));
                    if (properties == null) {
                        continue;
                    }
                    historyRecords.add(new FigureRecord(
                            directory,
                            properties.getProperty("title", "Untitled figure"),
                            longValue(properties, "modifiedAt", directory.lastModified()),
                            intValue(properties, "crop.count", 0)));
                }
            }
            Collections.sort(historyRecords, new Comparator<FigureRecord>() {
                @Override
                public int compare(FigureRecord left, FigureRecord right) {
                    return Long.compare(right.modifiedAt, left.modifiedAt);
                }
            });
            historyModel.setRowCount(0);
            DateFormat dateFormat = new SimpleDateFormat("yyyy-MM-dd  HH:mm");
            for (FigureRecord record : historyRecords) {
                historyModel.addRow(new Object[] {
                    record.title,
                    dateFormat.format(new Date(record.modifiedAt)),
                    Integer.valueOf(record.cropCount)
                });
            }
            if (!historyRecords.isEmpty()) {
                historyTable.setRowSelectionInterval(0, 0);
            }
        }

        private FigureRecord selectedHistoryRecord() {
            int row = historyTable == null ? -1 : historyTable.getSelectedRow();
            if (row < 0 || row >= historyRecords.size()) {
                JOptionPane.showMessageDialog(frame, "Select a figure from the recent list first.",
                        "GelAnno", JOptionPane.INFORMATION_MESSAGE);
                return null;
            }
            return historyRecords.get(row);
        }

        private void openSelectedHistoryFigure() {
            FigureRecord record = selectedHistoryRecord();
            if (record == null) {
                return;
            }
            if (!loadProject(record.directory)) {
                JOptionPane.showMessageDialog(frame, "This saved figure could not be opened.",
                        "GelAnno", JOptionPane.ERROR_MESSAGE);
                return;
            }
            cards.show(cardPanel, CARD_EDITOR);
            frame.setTitle("GelAnno - " + figureTitle());
            setStatus("Saved figure opened. Changes are saved automatically.");
        }

        private void viewSelectedHistoryLog() {
            FigureRecord record = selectedHistoryRecord();
            if (record == null) {
                return;
            }
            Properties properties = readProperties(new File(record.directory, "project.properties"));
            if (properties != null) {
                showCoordinateLog(coordinateLog(properties), record.title + " - Coordinate Log");
            }
        }

        private void copySelectedHistoryLog() {
            FigureRecord record = selectedHistoryRecord();
            if (record == null) {
                return;
            }
            Properties properties = readProperties(new File(record.directory, "project.properties"));
            if (properties != null) {
                copyText(coordinateLog(properties), "Coordinate log copied to the clipboard.");
            }
        }

        private void deleteSelectedHistoryFigure() {
            FigureRecord record = selectedHistoryRecord();
            if (record == null) {
                return;
            }
            int answer = JOptionPane.showConfirmDialog(frame,
                    "Delete \"" + record.title + "\" and its saved crops?\n"
                            + "This cannot be undone.",
                    "Delete past figure", JOptionPane.YES_NO_OPTION,
                    JOptionPane.WARNING_MESSAGE);
            if (answer != JOptionPane.YES_OPTION) {
                return;
            }
            try {
                File root = historyRoot().getCanonicalFile();
                File target = record.directory.getCanonicalFile();
                File parent = target.getParentFile();
                if (parent == null || !parent.equals(root)) {
                    throw new IOException("The selected folder is outside GelAnno history.");
                }
                if (!deleteRecursively(target)) {
                    throw new IOException("One or more saved files could not be removed.");
                }
                if (target.getName().equals(projectId)) {
                    projectId = null;
                    bands.clear();
                    kdaMarkers.clear();
                    selectedBand = null;
                    figureCanvas.refreshLayout();
                }
                refreshHistory();
                setStatus("Past figure deleted from GelAnno history.");
            } catch (IOException ex) {
                JOptionPane.showMessageDialog(frame,
                        "Could not delete the selected figure.\n" + ex.getMessage(),
                        "Delete past figure", JOptionPane.ERROR_MESSAGE);
            }
        }

        private boolean deleteRecursively(File file) {
            if (file.isDirectory() && !Files.isSymbolicLink(file.toPath())) {
                File[] children = file.listFiles();
                if (children == null) {
                    return false;
                }
                for (File child : children) {
                    if (!deleteRecursively(child)) {
                        return false;
                    }
                }
            }
            return file.delete();
        }

        private void showCoordinateLog(String text, String title) {
            JTextArea area = new JTextArea(text, 24, 74);
            area.setEditable(false);
            area.setCaretPosition(0);
            area.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
            JOptionPane.showMessageDialog(frame, new JScrollPane(area), title,
                    JOptionPane.INFORMATION_MESSAGE);
        }

        private void copyText(String text, String message) {
            Toolkit.getDefaultToolkit().getSystemClipboard().setContents(
                    new StringSelection(text == null ? "" : text), null);
            setStatus(message);
        }

        private String figureTitle() {
            if (figureTitleField == null || figureTitleField.getText().trim().length() == 0) {
                return "Untitled figure";
            }
            return figureTitleField.getText().trim();
        }

        private boolean saveProject(boolean announce) {
            if (projectId == null || figureTitleField == null) {
                return true;
            }
            File directory = new File(historyRoot(), projectId);
            if (!directory.exists() && !directory.mkdirs()) {
                if (announce) {
                    setStatus("Could not create the GelAnno history folder.");
                }
                return false;
            }
            Properties properties = new Properties();
            long now = System.currentTimeMillis();
            properties.setProperty("format.version", "1");
            properties.setProperty("id", projectId);
            properties.setProperty("title", figureTitle());
            properties.setProperty("createdAt", Long.toString(projectCreatedAt));
            properties.setProperty("modifiedAt", Long.toString(now));
            properties.setProperty("gel.path", gelImagePath == null ? "" : gelImagePath);
            properties.setProperty("marker.path", markerImagePath == null ? "" : markerImagePath);
            properties.setProperty("marker.count", Integer.toString(kdaMarkers.size()));
            for (int i = 0; i < kdaMarkers.size(); i++) {
                KdaMarker marker = kdaMarkers.get(i);
                String key = "marker." + i + ".";
                properties.setProperty(key + "label", marker.label);
                properties.setProperty(key + "x", Double.toString(marker.xAbs));
                properties.setProperty(key + "y", Double.toString(marker.yAbs));
            }
            properties.setProperty("crop.count", Integer.toString(bands.size()));
            try {
                for (int i = 0; i < bands.size(); i++) {
                    BandCrop band = bands.get(i);
                    String key = "crop." + i + ".";
                    String imageName = String.format("crop-%03d.png", Integer.valueOf(i + 1));
                    properties.setProperty(key + "image", imageName);
                    properties.setProperty(key + "label", band.label);
                    properties.setProperty(key + "displayWidth", Integer.toString(band.displayWidth));
                    properties.setProperty(key + "xOffset", Double.toString(band.xOffset));
                    properties.setProperty(key + "yOffset", Double.toString(band.yOffset));
                    properties.setProperty(key + "x", Double.toString(band.cropX));
                    properties.setProperty(key + "y", Double.toString(band.cropY));
                    properties.setProperty(key + "width", Integer.toString(band.cropWidth));
                    properties.setProperty(key + "height", Integer.toString(band.cropHeight));
                    properties.setProperty(key + "angle", Double.toString(band.cropAngleDeg));
                    properties.setProperty(key + "marker.count", Integer.toString(band.markers.size()));
                    for (int m = 0; m < band.markers.size(); m++) {
                        CropMarker marker = band.markers.get(m);
                        String markerKey = key + "marker." + m + ".";
                        properties.setProperty(markerKey + "label", marker.label);
                        properties.setProperty(markerKey + "cropY", Double.toString(marker.yInCrop));
                        properties.setProperty(markerKey + "x", Double.toString(marker.xAbs));
                        properties.setProperty(markerKey + "y", Double.toString(marker.yAbs));
                    }
                    ImageIO.write(band.image, "png", new File(directory, imageName));
                }
                BufferedOutputStream output = new BufferedOutputStream(
                        new FileOutputStream(new File(directory, "project.properties")));
                try {
                    properties.store(output, "GelAnno figure history");
                } finally {
                    output.close();
                }
                if (announce) {
                    setStatus("Figure saved to GelAnno history.");
                }
                frame.setTitle("GelAnno - " + figureTitle());
                return true;
            } catch (IOException ex) {
                if (announce) {
                    JOptionPane.showMessageDialog(frame, "Could not save the figure history.\n" + ex.getMessage(),
                            "GelAnno", JOptionPane.ERROR_MESSAGE);
                }
                return false;
            }
        }

        private boolean loadProject(File directory) {
            Properties properties = readProperties(new File(directory, "project.properties"));
            if (properties == null) {
                return false;
            }
            cancelCropMode();
            if (kdaModeActive) {
                deactivateKdaMode();
            }
            bands.clear();
            kdaMarkers.clear();
            selectedBand = null;
            gelImp = null;
            markerImp = null;
            projectId = properties.getProperty("id", directory.getName());
            projectCreatedAt = longValue(properties, "createdAt", directory.lastModified());
            gelImagePath = properties.getProperty("gel.path", "");
            markerImagePath = properties.getProperty("marker.path", "");
            figureTitleField.setText(properties.getProperty("title", "Untitled figure"));

            int markerCount = intValue(properties, "marker.count", 0);
            for (int i = 0; i < markerCount; i++) {
                String key = "marker." + i + ".";
                kdaMarkers.add(new KdaMarker(
                        doubleValue(properties, key + "x", 0.0),
                        doubleValue(properties, key + "y", 0.0),
                        properties.getProperty(key + "label", "")));
            }
            int cropCount = intValue(properties, "crop.count", 0);
            try {
                for (int i = 0; i < cropCount; i++) {
                    String key = "crop." + i + ".";
                    BufferedImage image = ImageIO.read(new File(directory,
                            properties.getProperty(key + "image", String.format(
                                    "crop-%03d.png", Integer.valueOf(i + 1)))));
                    if (image == null) {
                        return false;
                    }
                    List<CropMarker> markers = new ArrayList<CropMarker>();
                    int localMarkerCount = intValue(properties, key + "marker.count", 0);
                    for (int m = 0; m < localMarkerCount; m++) {
                        String markerKey = key + "marker." + m + ".";
                        markers.add(new CropMarker(
                                properties.getProperty(markerKey + "label", ""),
                                doubleValue(properties, markerKey + "cropY", 0.0),
                                doubleValue(properties, markerKey + "x", 0.0),
                                doubleValue(properties, markerKey + "y", 0.0)));
                    }
                    BandCrop band = new BandCrop(image, markers,
                            properties.getProperty(key + "label", "Protein"),
                            intValue(properties, key + "displayWidth", image.getWidth()));
                    band.xOffset = doubleValue(properties, key + "xOffset", 0.0);
                    band.yOffset = doubleValue(properties, key + "yOffset", 0.0);
                    band.cropX = doubleValue(properties, key + "x", 0.0);
                    band.cropY = doubleValue(properties, key + "y", 0.0);
                    band.cropWidth = intValue(properties, key + "width", image.getWidth());
                    band.cropHeight = intValue(properties, key + "height", image.getHeight());
                    band.cropAngleDeg = doubleValue(properties, key + "angle", 0.0);
                    bands.add(band);
                }
            } catch (IOException ex) {
                return false;
            }
            if (!bands.isEmpty()) {
                selectedBand = bands.get(0);
            }
            figureCanvas.refreshLayout();
            return true;
        }

        private Properties readProperties(File file) {
            if (!file.isFile()) {
                return null;
            }
            Properties properties = new Properties();
            try {
                BufferedInputStream input = new BufferedInputStream(new FileInputStream(file));
                try {
                    properties.load(input);
                } finally {
                    input.close();
                }
                return properties;
            } catch (IOException ex) {
                return null;
            }
        }

        private static int intValue(Properties properties, String key, int fallback) {
            try {
                return Integer.parseInt(properties.getProperty(key, Integer.toString(fallback)));
            } catch (NumberFormatException ex) {
                return fallback;
            }
        }

        private static long longValue(Properties properties, String key, long fallback) {
            try {
                return Long.parseLong(properties.getProperty(key, Long.toString(fallback)));
            } catch (NumberFormatException ex) {
                return fallback;
            }
        }

        private static double doubleValue(Properties properties, String key, double fallback) {
            try {
                return Double.parseDouble(properties.getProperty(key, Double.toString(fallback)));
            } catch (NumberFormatException ex) {
                return fallback;
            }
        }

        private String coordinateLog() {
            StringBuilder log = new StringBuilder();
            log.append("GelAnno Coordinate Log\n");
            log.append("Figure: ").append(figureTitle()).append('\n');
            if (gelImagePath != null && gelImagePath.length() > 0) {
                log.append("Gel image: ").append(gelImagePath).append('\n');
            }
            log.append("Crops: ").append(bands.size()).append("\n\n");
            for (int i = 0; i < bands.size(); i++) {
                appendBandLog(log, i, bands.get(i));
            }
            return log.toString();
        }

        private String coordinateLog(Properties properties) {
            StringBuilder log = new StringBuilder();
            log.append("GelAnno Coordinate Log\n");
            log.append("Figure: ").append(properties.getProperty("title", "Untitled figure")).append('\n');
            String gelPath = properties.getProperty("gel.path", "");
            if (gelPath.length() > 0) {
                log.append("Gel image: ").append(gelPath).append('\n');
            }
            int cropCount = intValue(properties, "crop.count", 0);
            log.append("Crops: ").append(cropCount).append("\n\n");
            for (int i = 0; i < cropCount; i++) {
                String key = "crop." + i + ".";
                log.append("Crop ").append(i + 1).append(": ")
                        .append(properties.getProperty(key + "label", "Protein")).append('\n');
                log.append("  x=").append(formatCoordinate(doubleValue(properties, key + "x", 0.0)))
                        .append(", y=").append(formatCoordinate(doubleValue(properties, key + "y", 0.0)))
                        .append(", width=").append(intValue(properties, key + "width", 0))
                        .append(", height=").append(intValue(properties, key + "height", 0))
                        .append(", angle=").append(formatCoordinate(
                                doubleValue(properties, key + "angle", 0.0))).append(" deg\n");
                int markerCount = intValue(properties, key + "marker.count", 0);
                for (int m = 0; m < markerCount; m++) {
                    String markerKey = key + "marker." + m + ".";
                    log.append("  marker ").append(properties.getProperty(markerKey + "label", ""))
                            .append(": x=").append(formatCoordinate(
                                    doubleValue(properties, markerKey + "x", 0.0)))
                            .append(", y=").append(formatCoordinate(
                                    doubleValue(properties, markerKey + "y", 0.0)))
                            .append(", cropY=").append(formatCoordinate(
                                    doubleValue(properties, markerKey + "cropY", 0.0))).append('\n');
                }
                log.append('\n');
            }
            return log.toString();
        }

        private void appendBandLog(StringBuilder log, int index, BandCrop band) {
            log.append("Crop ").append(index + 1).append(": ").append(band.label).append('\n');
            log.append("  x=").append(formatCoordinate(band.cropX))
                    .append(", y=").append(formatCoordinate(band.cropY))
                    .append(", width=").append(band.cropWidth)
                    .append(", height=").append(band.cropHeight)
                    .append(", angle=").append(formatCoordinate(band.cropAngleDeg)).append(" deg\n");
            for (CropMarker marker : band.markers) {
                log.append("  marker ").append(marker.label)
                        .append(": x=").append(formatCoordinate(marker.xAbs))
                        .append(", y=").append(formatCoordinate(marker.yAbs))
                        .append(", cropY=").append(formatCoordinate(marker.yInCrop)).append('\n');
            }
            log.append('\n');
        }

        private static String formatCoordinate(double value) {
            return String.format(Locale.US, "%.2f", Double.valueOf(value));
        }

        private void editSelectedCoordinates() {
            if (selectedBand == null) {
                JOptionPane.showMessageDialog(frame, "Select a crop in the figure first.",
                        "Edit coordinates", JOptionPane.INFORMATION_MESSAGE);
                return;
            }
            final BandCrop band = selectedBand;
            JTextField label = new JTextField(band.label);
            JTextField x = new JTextField(Double.toString(band.cropX));
            JTextField y = new JTextField(Double.toString(band.cropY));
            JTextField width = new JTextField(Integer.toString(band.cropWidth));
            JTextField height = new JTextField(Integer.toString(band.cropHeight));
            JTextField angle = new JTextField(Double.toString(band.cropAngleDeg));
            JPanel fields = new JPanel(new GridLayout(0, 2, 8, 6));
            fields.add(new JLabel("Crop label"));
            fields.add(label);
            fields.add(new JLabel("Source X"));
            fields.add(x);
            fields.add(new JLabel("Source Y"));
            fields.add(y);
            fields.add(new JLabel("Source width"));
            fields.add(width);
            fields.add(new JLabel("Source height"));
            fields.add(height);
            fields.add(new JLabel("Rotation angle (degrees)"));
            fields.add(angle);
            int result = JOptionPane.showConfirmDialog(frame, fields,
                    "Edit selected crop coordinates", JOptionPane.OK_CANCEL_OPTION,
                    JOptionPane.PLAIN_MESSAGE);
            if (result != JOptionPane.OK_OPTION) {
                return;
            }
            try {
                double newX = Double.parseDouble(x.getText().trim());
                double newY = Double.parseDouble(y.getText().trim());
                int newWidth = Integer.parseInt(width.getText().trim());
                int newHeight = Integer.parseInt(height.getText().trim());
                double newAngle = Double.parseDouble(angle.getText().trim());
                if (newWidth < 1 || newHeight < 1) {
                    throw new NumberFormatException("Width and height must be positive.");
                }
                band.label = label.getText().trim().length() == 0 ? "Protein" : label.getText().trim();
                band.cropX = newX;
                band.cropY = newY;
                band.cropWidth = newWidth;
                band.cropHeight = newHeight;
                band.cropAngleDeg = newAngle;
                figureCanvas.repaint();
                saveProject(false);
                setStatus("Crop coordinates updated and saved.");
            } catch (NumberFormatException ex) {
                JOptionPane.showMessageDialog(frame,
                        "Enter numeric values for X, Y, width, height, and angle.",
                        "Invalid coordinates", JOptionPane.WARNING_MESSAGE);
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
            if (markerImp == null) {
                clearOverlay(gelImp);
            }
            gelImp = imp;
            gelImagePath = openedImagePath;
            if (markerImp == null) {
                kdaMarkers.clear();
            }
            showImageRightHalf(imp);
            activateGelImage();
            setCropSelectionTool();
            setStatus(markerImp == null
                    ? "Gel loaded. Mark kDa bands on it, or open a separate kDa marker image."
                    : "Gel loaded. Existing markers from the kDa marker image will be applied to crops.");
            saveProject(false);
        }

        private void openMarkerImage() {
            ImagePlus imp = openRgbImage();
            if (imp == null) {
                return;
            }
            cancelCropMode();
            if (kdaModeActive) {
                deactivateKdaMode();
            }
            clearOverlay(kdaSourceImage());
            markerImp = imp;
            markerImagePath = openedImagePath;
            kdaMarkers.clear();
            showImageRightHalf(imp);
            setCropSelectionTool();
            setStatus("kDa marker image loaded. Click Mark kDa Bands, then click its marker bands.");
            saveProject(false);
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
            openedImagePath = chosen.getAbsolutePath();
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
            if (kdaSourceImage() == null) {
                JOptionPane.showMessageDialog(frame, "Open a gel image or a kDa marker image first.",
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
            final ImagePlus source = kdaSourceImage();
            if (source == null || source.getCanvas() == null) {
                return;
            }
            kdaModeActive = true;
            markButton.setText("Stop Marking kDa");
            markButton.setBackground(new Color(255, 180, 0));
            setStatus(markerImp == null
                    ? "kDa marking active. Click a marker band in the gel image."
                    : "kDa marking active. Click a marker band in the separate marker image.");
            IJ.setTool("point");

            final ImageCanvas canvas = source.getCanvas();
            // ImageJ treats a press held while our label dialog is open as a long click
            // and shows its canvas context menu. Disable that menu only while marking.
            canvas.disablePopupMenu(true);
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
            kdaCanvas = canvas;
            canvas.addMouseListener(gelMouseListener);
        }

        private void deactivateKdaMode() {
            kdaModeActive = false;
            markButton.setText("Mark kDa Bands");
            markButton.setBackground(null);
            if (kdaCanvas != null && gelMouseListener != null) {
                kdaCanvas.removeMouseListener(gelMouseListener);
            }
            if (kdaCanvas != null) {
                kdaCanvas.disablePopupMenu(false);
            }
            gelMouseListener = null;
            kdaCanvas = null;
            setCropSelectionTool();
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
            saveProject(false);
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
            ImagePlus source = kdaSourceImage();
            if (source == null) {
                return;
            }
            if (kdaMarkers.isEmpty()) {
                clearOverlay(source);
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
            source.setOverlay(overlay);
            source.updateAndDraw();
        }

        private ImagePlus kdaSourceImage() {
            return markerImp != null ? markerImp : gelImp;
        }

        private void clearOverlay(ImagePlus imp) {
            if (imp != null) {
                imp.setOverlay(null);
                imp.updateAndDraw();
            }
        }

        private void undoLastKda() {
            if (!kdaMarkers.isEmpty()) {
                kdaMarkers.remove(kdaMarkers.size() - 1);
                redrawKdaOverlay();
                saveProject(false);
            }
        }

        private void clearAllKda() {
            kdaMarkers.clear();
            redrawKdaOverlay();
            saveProject(false);
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
                cropWasMarking = kdaModeActive;
                if (kdaModeActive) {
                    deactivateKdaMode();
                }
                activateGelImage();
                if (!setCropSelectionTool()) {
                    cropButton.setText("Crop Region -> Figure");
                    cropButton.setBackground(null);
                    JOptionPane.showMessageDialog(frame,
                            "Fiji could not activate the Rotated Rectangle tool. "
                                    + "Please restart Fiji and try again.",
                            "Crop tool unavailable", JOptionPane.ERROR_MESSAGE);
                    restoreCropMarkMode();
                    return;
                }
                if (gelImp.getRoi() == null) {
                    waitingForCrop = true;
                    cropButton.setText("Confirm Crop");
                    cropButton.setBackground(new Color(255, 180, 0));
                    setStatus("Draw and rotate the crop rectangle, then click Confirm Crop.");
                    return;
                }
            }

            Roi roi = gelImp.getRoi();
            if (roi == null) {
                JOptionPane.showMessageDialog(frame, "No selection found. Click Crop again and draw first.",
                        "No selection", JOptionPane.WARNING_MESSAGE);
                activateGelImage();
                setCropSelectionTool();
                setStatus("Crop mode is still active. Draw a crop on the source image, then click Confirm Crop.");
                return;
            }
            styleCropRoi(roi);
            CropResult crop = rotatedCropFromRoi(gelImp, roi);
            if (crop == null) {
                JOptionPane.showMessageDialog(frame, "Selection is too small. Please try again.",
                        "Crop", JOptionPane.WARNING_MESSAGE);
                gelImp.killRoi();
                activateGelImage();
                setCropSelectionTool();
                setStatus("Crop mode is still active. Draw a larger crop, then click Confirm Crop.");
                return;
            }
            waitingForCrop = false;
            cropButton.setText("Crop Region -> Figure");
            cropButton.setBackground(null);

            List<CropMarker> localMarkers = new ArrayList<CropMarker>();
            for (KdaMarker marker : kdaMarkers) {
                Point2D markerOnGel = markerInGelCoordinates(marker);
                double yInCrop = markerYInCrop(
                        markerOnGel.x, markerOnGel.y, crop.x, crop.y, crop.angleDeg);
                if (yInCrop >= -0.5 && yInCrop <= crop.height + 0.5) {
                    localMarkers.add(new CropMarker(
                            marker.label, yInCrop, markerOnGel.x, markerOnGel.y));
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
            saveProject(false);
            gelImp.killRoi();
            activateGelImage();
            setCropSelectionTool();
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

        private void activateGelImage() {
            if (gelImp == null) {
                return;
            }
            if (gelImp.getWindow() != null) {
                WindowManager.setCurrentWindow(gelImp.getWindow());
                gelImp.getWindow().toFront();
            }
            if (gelImp.getCanvas() != null) {
                gelImp.getCanvas().requestFocusInWindow();
            }
        }

        private boolean setCropSelectionTool() {
            Roi.setColor(CROP_COLOR);
            trySetDefaultRoiStrokeWidth(CROP_STROKE_WIDTH);
            Toolbar toolbar = Toolbar.getInstance();
            if (toolbar == null || !toolbar.setTool("rotated rectangle")) {
                return false;
            }
            return Toolbar.getToolId() == Toolbar.RECTANGLE
                    && Toolbar.getRectToolType() == Toolbar.ROTATED_RECT_ROI;
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

        private Point2D markerInGelCoordinates(KdaMarker marker) {
            if (gelImp == null || markerImp == null || markerImp == gelImp) {
                return new Point2D(marker.xAbs, marker.yAbs);
            }
            double scaleX = gelImp.getWidth() / (double) markerImp.getWidth();
            double scaleY = gelImp.getHeight() / (double) markerImp.getHeight();
            return new Point2D(marker.xAbs * scaleX, marker.yAbs * scaleY);
        }

        private static double markerYInCrop(double markerX, double markerY,
                double cropX, double cropY,
                double cropAngleDeg) {
            double angle = Math.toRadians(cropAngleDeg);
            double dx = markerX - cropX;
            double dy = markerY - cropY;
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
            saveProject(false);
            setStatus("Crop resized. kDa ticks were recomputed from the crop scale.");
        }

        private void clearFigure() {
            bands.clear();
            selectedBand = null;
            figureCanvas.refreshLayout();
            saveProject(false);
        }

        private void exportPdf() {
            if (bands.isEmpty()) {
                JOptionPane.showMessageDialog(frame, "Nothing to export.",
                        "Export PDF", JOptionPane.WARNING_MESSAGE);
                return;
            }
            saveProject(false);
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

        private void figureLayoutChanged() {
            saveProject(false);
            setStatus("Figure layout updated and saved.");
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
                    if (dragBand != null) {
                        controller.figureLayoutChanged();
                    }
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
                boolean showSelection = paintBackground && band == controller.selectedBand();
                drawBand(g, band, rect, showSelection);
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

    private static final class Point2D {
        final double x;
        final double y;

        Point2D(double x, double y) {
            this.x = x;
            this.y = y;
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
        String label;
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

    private static final class FigureRecord {
        final File directory;
        final String title;
        final long modifiedAt;
        final int cropCount;

        FigureRecord(File directory, String title, long modifiedAt, int cropCount) {
            this.directory = directory;
            this.title = title;
            this.modifiedAt = modifiedAt;
            this.cropCount = cropCount;
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
