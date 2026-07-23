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
import java.awt.FlowLayout;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Point;
import java.awt.Rectangle;
import java.awt.RenderingHints;
import java.awt.Toolkit;
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
import java.awt.datatransfer.StringSelection;
import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.LinkedHashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.UUID;
import javax.imageio.ImageIO;
import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JDialog;
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
import javax.swing.WindowConstants;
import javax.swing.filechooser.FileNameExtensionFilter;
import javax.swing.table.DefaultTableModel;
import org.scijava.command.Command;
import org.scijava.plugin.Plugin;

@Plugin(type = Command.class, menuPath = "Plugins>GelAnno>GelAnno 0.3.0-alpha")
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
        private static final String VERSION = "0.3.0-alpha";
        private static final int LOG_FORMAT_VERSION = 1;
        private static final String TITLE = "GelAnno " + VERSION;
        private static final String CARD_HOME = "home";
        private static final String CARD_EDITOR = "editor";
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
        private JLabel activeMarkerSetLabel;
        private FigureCanvas figureCanvas;
        private CardLayout cards;
        private JPanel cardPanel;
        private DefaultTableModel historyModel;
        private JTable historyTable;
        private JTextField figureTitleField;

        private ImagePlus gelImp;
        private ImagePlus markerImp;
        private String gelPath;
        private String markerPath;
        private File lastDir;
        private final List<KdaMarkerSet> markerSets = new ArrayList<KdaMarkerSet>();
        private final List<BandCrop> bands = new ArrayList<BandCrop>();
        private final List<AnnotatedMarkerImage> annotatedMarkerImages =
                new ArrayList<AnnotatedMarkerImage>();
        private final Set<String> shownMappingWarnings = new HashSet<String>();
        private final String windowTitle;
        private final boolean startOnHome;
        private final List<FigureRecord> historyRecords = new ArrayList<FigureRecord>();
        private String projectId;
        private long projectCreatedAt;

        private KdaMarkerSet activeMarkerSet;
        private MarkerSourceType markingSourceType;
        private boolean startFreshMarkerSetOnNextMark;
        private int nextMarkerSetNumber = 1;

        private boolean kdaModeActive;
        private boolean showSourceKdaLabels = true;
        private boolean waitingForCrop;
        private boolean cropWasMarking;
        private MouseListener gelMouseListener;
        private ImageCanvas kdaCanvas;
        private BandCrop selectedBand;

        public Controller() {
            this(TITLE, true);
        }

        private Controller(String windowTitle) {
            this(windowTitle, false);
        }

        private Controller(String windowTitle, boolean startOnHome) {
            this.windowTitle = windowTitle;
            this.startOnHome = startOnHome;
        }

        public void showFrame() {
            if (frame == null) {
                buildUi();
            }
            frame.setVisible(true);
            frame.toFront();
        }

        private void buildUi() {
            frame = new JFrame(windowTitle);
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
            if (startOnHome) {
                showHome();
            } else {
                beginUnsavedFigure("Reconstructed figure");
                cards.show(cardPanel, CARD_EDITOR);
            }
        }

        private JPanel buildHomePanel() {
            JPanel home = new JPanel(new BorderLayout(12, 12));
            home.setBorder(BorderFactory.createEmptyBorder(24, 28, 24, 28));
            JPanel heading = new JPanel();
            heading.setLayout(new BoxLayout(heading, BoxLayout.Y_AXIS));
            JLabel title = new JLabel("GelAnno");
            title.setFont(title.getFont().deriveFont(Font.BOLD, 28.0f));
            heading.add(title);
            heading.add(Box.createVerticalStrut(4));
            heading.add(new JLabel("Recent figures and coordinate logs"));
            heading.add(Box.createVerticalStrut(18));
            JButton blank = homeButton("+  New Figure", "new_figure");
            blank.setPreferredSize(new Dimension(180, 70));
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

            JPanel actions = new JPanel(new FlowLayout(FlowLayout.RIGHT));
            actions.add(homeButton("Open / Edit", "open_history"));
            actions.add(homeButton("View Coordinate Log", "view_history_log"));
            actions.add(homeButton("Copy Coordinates", "copy_history_log"));
            actions.add(homeButton("Delete", "delete_history"));
            actions.add(homeButton("Refresh", "refresh_history"));
            home.add(actions, BorderLayout.SOUTH);
            return home;
        }

        private JButton homeButton(String label, String command) {
            JButton result = new JButton(label);
            result.setActionCommand(command);
            result.addActionListener(this);
            return result;
        }

        private JPanel buildEditorPanel() {
            JPanel editor = new JPanel(new BorderLayout(8, 8));

            JPanel tools = new JPanel();
            tools.setLayout(new BoxLayout(tools, BoxLayout.Y_AXIS));
            tools.setBorder(BorderFactory.createEmptyBorder(10, 10, 10, 6));

            addSection(tools, "GelAnno");
            tools.add(button("Back to Home", "home"));
            tools.add(button("New Figure", "new_figure"));
            tools.add(Box.createVerticalStrut(8));

            addSection(tools, "kDa Markers");
            tools.add(button("Open kDa Marker Image...", "open_marker_image"));
            markButton = button("Mark kDa Bands", "toggle_mark_kda");
            tools.add(markButton);
            sourceKdaLabelsButton = button("Hide kDa Labels", "toggle_source_kda_labels");
            tools.add(sourceKdaLabelsButton);
            tools.add(button("Undo Last kDa", "undo_kda"));
            tools.add(button("Clear All kDa", "clear_kda"));
            activeMarkerSetLabel = new JLabel("Active markers: none");
            Dimension markerLabelSize = new Dimension(TOOL_BUTTON_W, 24);
            activeMarkerSetLabel.setMinimumSize(markerLabelSize);
            activeMarkerSetLabel.setPreferredSize(markerLabelSize);
            activeMarkerSetLabel.setMaximumSize(markerLabelSize);
            tools.add(activeMarkerSetLabel);
            tools.add(Box.createVerticalStrut(8));

            addSection(tools, "Image");
            tools.add(button("Open Gel Image...", "open_image"));
            tools.add(Box.createVerticalStrut(8));

            addSection(tools, "Crop");
            cropButton = button("Crop Region -> Figure", "crop");
            tools.add(cropButton);
            tools.add(Box.createVerticalStrut(8));

            addSection(tools, "Figure");
            tools.add(button("Wider", "wider"));
            tools.add(button("Narrower", "narrower"));
            tools.add(button("Show Coordinate Log", "show_coordinate_log"));
            tools.add(button("Reconstruct from Log...", "reconstruct_from_log"));
            tools.add(button("Clear Figure", "clear_figure"));
            tools.add(Box.createVerticalStrut(8));

            addSection(tools, "Export");
            tools.add(button("Export as PDF...", "export_pdf"));
            tools.add(Box.createVerticalGlue());

            figureCanvas = new FigureCanvas(this);
            JScrollPane scrollPane = new JScrollPane(figureCanvas);
            scrollPane.setPreferredSize(new Dimension(FIG_INIT_W, 620));

            JScrollPane toolsScroll = new JScrollPane(tools,
                    JScrollPane.VERTICAL_SCROLLBAR_ALWAYS,
                    JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);
            toolsScroll.setBorder(null);
            toolsScroll.setPreferredSize(new Dimension(TOOL_BUTTON_W + 42, 620));
            toolsScroll.getVerticalScrollBar().setUnitIncrement(16);

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
            editor.add(toolsScroll, BorderLayout.WEST);
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
            if ("home".equals(command)) {
                saveProject(false);
                showHome();
            } else if ("new_figure".equals(command)) {
                newFigure();
            } else if ("open_history".equals(command)) {
                openSelectedHistoryFigure();
            } else if ("view_history_log".equals(command)) {
                viewSelectedHistoryLog();
            } else if ("copy_history_log".equals(command)) {
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
            } else if ("show_coordinate_log".equals(command)) {
                showCoordinateLog();
            } else if ("reconstruct_from_log".equals(command)) {
                showReconstructionLogDialog();
            } else if ("clear_figure".equals(command)) {
                clearFigure();
            } else if ("export_pdf".equals(command)) {
                exportPdf();
            }
        }

        private void beginUnsavedFigure(String title) {
            projectId = UUID.randomUUID().toString();
            projectCreatedAt = System.currentTimeMillis();
            if (figureTitleField != null) {
                figureTitleField.setText(title == null || title.trim().length() == 0
                        ? "Untitled figure" : title.trim());
            }
        }

        private void newFigure() {
            saveProject(false);
            resetFigureState();
            beginUnsavedFigure("Untitled figure");
            cards.show(cardPanel, CARD_EDITOR);
            frame.setTitle(TITLE + " - " + figureTitle());
            figureCanvas.refreshLayout();
            saveProject(false);
            setStatus("New figure created. Changes are saved automatically.");
        }

        private void resetFigureState() {
            cancelCropMode();
            if (kdaModeActive) {
                deactivateKdaMode();
            }
            clearOverlay(gelImp);
            clearOverlay(markerImp);
            gelImp = null;
            markerImp = null;
            gelPath = null;
            markerPath = null;
            markerSets.clear();
            bands.clear();
            annotatedMarkerImages.clear();
            shownMappingWarnings.clear();
            activeMarkerSet = null;
            markingSourceType = null;
            startFreshMarkerSetOnNextMark = false;
            nextMarkerSetNumber = 1;
            selectedBand = null;
            updateActiveMarkerSetLabel();
        }

        private String figureTitle() {
            if (figureTitleField == null || figureTitleField.getText().trim().length() == 0) {
                return "Untitled figure";
            }
            return figureTitleField.getText().trim();
        }

        private void showHome() {
            refreshHistory();
            cards.show(cardPanel, CARD_HOME);
            frame.setTitle("GelAnno");
            setStatus("Select a recent figure, or create a new figure.");
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
                    if (properties != null) {
                        historyRecords.add(new FigureRecord(directory,
                                properties.getProperty("title", "Untitled figure"),
                                longValue(properties, "modifiedAt", directory.lastModified()),
                                intValue(properties, "crop.count", 0)));
                    }
                }
            }
            Collections.sort(historyRecords, new Comparator<FigureRecord>() {
                @Override
                public int compare(FigureRecord first, FigureRecord second) {
                    return Long.compare(second.modifiedAt, first.modifiedAt);
                }
            });
            historyModel.setRowCount(0);
            DateFormat dates = new SimpleDateFormat("yyyy-MM-dd  HH:mm");
            for (FigureRecord record : historyRecords) {
                historyModel.addRow(new Object[] {record.title,
                    dates.format(new Date(record.modifiedAt)), Integer.valueOf(record.cropCount)});
            }
            if (!historyRecords.isEmpty()) {
                historyTable.setRowSelectionInterval(0, 0);
            }
        }

        private FigureRecord selectedHistoryRecord() {
            int row = historyTable == null ? -1 : historyTable.getSelectedRow();
            if (row < 0 || row >= historyRecords.size()) {
                JOptionPane.showMessageDialog(frame, "Select a figure first.",
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
            saveProject(false);
            if (!loadProject(record.directory)) {
                JOptionPane.showMessageDialog(frame, "This saved figure could not be opened.",
                        "GelAnno", JOptionPane.ERROR_MESSAGE);
                return;
            }
            cards.show(cardPanel, CARD_EDITOR);
            frame.setTitle(TITLE + " - " + figureTitle());
            setStatus("Saved figure opened. Changes are saved automatically.");
        }

        private void viewSelectedHistoryLog() {
            FigureRecord record = selectedHistoryRecord();
            if (record == null) {
                return;
            }
            String log = readTextFile(new File(record.directory, "coordinate-log.txt"));
            if (log == null) {
                JOptionPane.showMessageDialog(frame,
                        "Open this figure once to generate its coordinate-log.txt file.",
                        "GelAnno Coordinate Log", JOptionPane.INFORMATION_MESSAGE);
                return;
            }
            showTextLog(record.title, log);
        }

        private void copySelectedHistoryLog() {
            FigureRecord record = selectedHistoryRecord();
            if (record == null) {
                return;
            }
            String log = readTextFile(new File(record.directory, "coordinate-log.txt"));
            if (log == null) {
                JOptionPane.showMessageDialog(frame,
                        "Open this figure once to generate its coordinate-log.txt file.",
                        "GelAnno Coordinate Log", JOptionPane.INFORMATION_MESSAGE);
                return;
            }
            Toolkit.getDefaultToolkit().getSystemClipboard()
                    .setContents(new StringSelection(log), null);
            setStatus("Coordinate log copied to the clipboard.");
        }

        private void showTextLog(String title, String text) {
            JTextArea area = new JTextArea(text, 34, 92);
            area.setEditable(false);
            area.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
            area.setLineWrap(false);
            area.setCaretPosition(0);
            JOptionPane.showMessageDialog(frame, new JScrollPane(area),
                    title + " - Coordinate Log", JOptionPane.INFORMATION_MESSAGE);
        }

        private String readTextFile(File file) {
            try {
                return file.isFile() ? new String(Files.readAllBytes(file.toPath()),
                        StandardCharsets.UTF_8) : null;
            } catch (IOException ex) {
                return null;
            }
        }

        private void deleteSelectedHistoryFigure() {
            FigureRecord record = selectedHistoryRecord();
            if (record == null) {
                return;
            }
            int answer = JOptionPane.showConfirmDialog(frame,
                    "Delete \"" + record.title + "\" and its saved crops?\nThis cannot be undone.",
                    "Delete past figure", JOptionPane.YES_NO_OPTION, JOptionPane.WARNING_MESSAGE);
            if (answer != JOptionPane.YES_OPTION) {
                return;
            }
            try {
                File root = historyRoot().getCanonicalFile();
                File target = record.directory.getCanonicalFile();
                if (target.getParentFile() == null || !target.getParentFile().equals(root)) {
                    throw new IOException("The selected folder is outside GelAnno history.");
                }
                if (!deleteRecursively(target)) {
                    throw new IOException("One or more saved files could not be removed.");
                }
                if (target.getName().equals(projectId)) {
                    projectId = null;
                    resetFigureState();
                }
                refreshHistory();
                setStatus("Past figure deleted from GelAnno history.");
            } catch (IOException ex) {
                JOptionPane.showMessageDialog(frame, "Could not delete the selected figure.\n"
                        + ex.getMessage(), "Delete past figure", JOptionPane.ERROR_MESSAGE);
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
            properties.setProperty("history.format", "2");
            properties.setProperty("id", projectId);
            properties.setProperty("title", figureTitle());
            properties.setProperty("createdAt", Long.toString(projectCreatedAt));
            properties.setProperty("modifiedAt", Long.toString(System.currentTimeMillis()));
            properties.setProperty("gel.path", gelPath == null ? "" : gelPath);
            properties.setProperty("marker.path", markerPath == null ? "" : markerPath);
            properties.setProperty("marking.sourceType",
                    markingSourceType == null ? "" : markingSourceType.name());
            properties.setProperty("marker.activeId",
                    activeMarkerSet == null ? "" : activeMarkerSet.id);
            properties.setProperty("marker.startFresh", Boolean.toString(startFreshMarkerSetOnNextMark));
            properties.setProperty("marker.nextNumber", Integer.toString(nextMarkerSetNumber));
            properties.setProperty("markerSet.count", Integer.toString(markerSets.size()));
            for (int i = 0; i < markerSets.size(); i++) {
                KdaMarkerSet set = markerSets.get(i);
                String key = "markerSet." + i + ".";
                properties.setProperty(key + "id", set.id);
                properties.setProperty(key + "sourceType", set.sourceType.name());
                properties.setProperty(key + "sourcePath", set.sourcePath == null ? "" : set.sourcePath);
                properties.setProperty(key + "sourceWidth", Integer.toString(set.sourceWidth));
                properties.setProperty(key + "sourceHeight", Integer.toString(set.sourceHeight));
                properties.setProperty(key + "frozen", Boolean.toString(set.frozen));
                properties.setProperty(key + "marker.count", Integer.toString(set.markers.size()));
                for (int m = 0; m < set.markers.size(); m++) {
                    KdaMarker marker = set.markers.get(m);
                    String markerKey = key + "marker." + m + ".";
                    properties.setProperty(markerKey + "label", marker.label);
                    properties.setProperty(markerKey + "x", Double.toString(marker.xAbs));
                    properties.setProperty(markerKey + "y", Double.toString(marker.yAbs));
                }
            }
            properties.setProperty("crop.count", Integer.toString(bands.size()));
            try {
                for (int i = 0; i < bands.size(); i++) {
                    BandCrop band = bands.get(i);
                    String key = "crop." + i + ".";
                    String imageName = String.format(Locale.US, "crop-%03d.png", Integer.valueOf(i + 1));
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
                    properties.setProperty(key + "sourcePath", band.sourcePath);
                    properties.setProperty(key + "sourceWidth", Integer.toString(band.sourceWidth));
                    properties.setProperty(key + "sourceHeight", Integer.toString(band.sourceHeight));
                    properties.setProperty(key + "markerSetId",
                            band.markerSet == null ? "" : band.markerSet.id);
                    if (band.markerMapping != null) {
                        MarkerMapping mapping = band.markerMapping;
                        properties.setProperty(key + "mapping.present", "true");
                        properties.setProperty(key + "mapping.markerWidth", Integer.toString(mapping.markerWidth));
                        properties.setProperty(key + "mapping.markerHeight", Integer.toString(mapping.markerHeight));
                        properties.setProperty(key + "mapping.gelWidth", Integer.toString(mapping.gelWidth));
                        properties.setProperty(key + "mapping.gelHeight", Integer.toString(mapping.gelHeight));
                        properties.setProperty(key + "mapping.scaleX", Double.toString(mapping.scaleX));
                        properties.setProperty(key + "mapping.scaleY", Double.toString(mapping.scaleY));
                        properties.setProperty(key + "mapping.dimensionsDiffer",
                                Boolean.toString(mapping.dimensionsDiffer));
                        properties.setProperty(key + "mapping.aspectRatioMismatch",
                                Boolean.toString(mapping.aspectRatioMismatch));
                    }
                    properties.setProperty(key + "marker.count", Integer.toString(band.markers.size()));
                    for (int m = 0; m < band.markers.size(); m++) {
                        CropMarker marker = band.markers.get(m);
                        String markerKey = key + "marker." + m + ".";
                        properties.setProperty(markerKey + "label", marker.label);
                        properties.setProperty(markerKey + "cropY", Double.toString(marker.yInCrop));
                        properties.setProperty(markerKey + "sourceX", Double.toString(marker.sourceXAbs));
                        properties.setProperty(markerKey + "sourceY", Double.toString(marker.sourceYAbs));
                        properties.setProperty(markerKey + "gelX", Double.toString(marker.gelXAbs));
                        properties.setProperty(markerKey + "gelY", Double.toString(marker.gelYAbs));
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
                Writer logWriter = new OutputStreamWriter(
                        new FileOutputStream(new File(directory, "coordinate-log.txt")),
                        StandardCharsets.UTF_8);
                try {
                    logWriter.write(buildCoordinateLog());
                } finally {
                    logWriter.close();
                }
                if (frame != null) {
                    frame.setTitle(TITLE + " - " + figureTitle());
                }
                if (announce) {
                    setStatus("Figure saved to GelAnno history.");
                }
                return true;
            } catch (IOException ex) {
                if (announce) {
                    JOptionPane.showMessageDialog(frame, "Could not save the figure history.\n"
                            + ex.getMessage(), "GelAnno", JOptionPane.ERROR_MESSAGE);
                }
                return false;
            }
        }

        private boolean loadProject(File directory) {
            Properties properties = readProperties(new File(directory, "project.properties"));
            if (properties == null) {
                return false;
            }
            resetFigureState();
            projectId = properties.getProperty("id", directory.getName());
            projectCreatedAt = longValue(properties, "createdAt", directory.lastModified());
            figureTitleField.setText(properties.getProperty("title", "Untitled figure"));
            gelPath = emptyToNull(properties.getProperty("gel.path", ""));
            markerPath = emptyToNull(properties.getProperty("marker.path", ""));
            markingSourceType = parseSourceType(properties.getProperty("marking.sourceType", ""), null);
            startFreshMarkerSetOnNextMark = Boolean.parseBoolean(
                    properties.getProperty("marker.startFresh", "false"));
            nextMarkerSetNumber = intValue(properties, "marker.nextNumber",
                    intValue(properties, "marker.nextSetNumber", 1));

            Map<String, KdaMarkerSet> setsById = new LinkedHashMap<String, KdaMarkerSet>();
            int setCount = intValue(properties, "markerSet.count", -1);
            if (setCount >= 0) {
                for (int i = 0; i < setCount; i++) {
                    String key = "markerSet." + i + ".";
                    String id = properties.getProperty(key + "id", "KDA-001");
                    KdaMarkerSet set = new KdaMarkerSet(id,
                            parseSourceType(properties.getProperty(key + "sourceType", ""),
                                    MarkerSourceType.GEL_IMAGE),
                            properties.getProperty(key + "sourcePath", ""),
                            intValue(properties, key + "sourceWidth", 0),
                            intValue(properties, key + "sourceHeight", 0));
                    set.frozen = Boolean.parseBoolean(properties.getProperty(key + "frozen", "false"));
                    int count = intValue(properties, key + "marker.count", 0);
                    for (int m = 0; m < count; m++) {
                        String markerKey = key + "marker." + m + ".";
                        set.markers.add(new KdaMarker(
                                doubleValue(properties, markerKey + "x", 0.0),
                                doubleValue(properties, markerKey + "y", 0.0),
                                properties.getProperty(markerKey + "label", "")));
                    }
                    markerSets.add(set);
                    setsById.put(id, set);
                }
            } else {
                loadLegacyMarkerSets(properties, setsById);
            }
            for (KdaMarkerSet set : markerSets) {
                nextMarkerSetNumber = Math.max(nextMarkerSetNumber,
                        markerSetNumber(set.id) + 1);
            }
            String activeId = properties.getProperty("marker.activeId",
                    properties.getProperty("marker.activeSetId", ""));
            activeMarkerSet = setsById.get(activeId);

            int cropCount = intValue(properties, "crop.count", 0);
            try {
                for (int i = 0; i < cropCount; i++) {
                    String key = "crop." + i + ".";
                    String defaultImage = String.format(Locale.US, "crop-%03d.png", Integer.valueOf(i + 1));
                    BufferedImage image = ImageIO.read(new File(directory,
                            properties.getProperty(key + "image", defaultImage)));
                    if (image == null) {
                        return false;
                    }
                    String markerSetId = properties.getProperty(key + "markerSetId",
                            properties.getProperty(key + "markerSet.id", ""));
                    KdaMarkerSet markerSet = setsById.get(markerSetId);
                    int sourceWidth = intValue(properties, key + "sourceWidth",
                            intValue(properties, key + "source.width", 0));
                    int sourceHeight = intValue(properties, key + "sourceHeight",
                            intValue(properties, key + "source.height", 0));
                    String sourcePath = properties.getProperty(key + "sourcePath",
                            properties.getProperty(key + "source.path",
                                    gelPath == null ? "" : gelPath));
                    if (sourceWidth <= 0 || sourceHeight <= 0) {
                        int[] dimensions = imageDimensions(sourcePath);
                        sourceWidth = dimensions[0];
                        sourceHeight = dimensions[1];
                    }
                    MarkerMapping mapping = loadMarkerMapping(properties, key, markerSet,
                            sourceWidth, sourceHeight);
                    List<CropMarker> cropMarkers = new ArrayList<CropMarker>();
                    int markerCount = intValue(properties, key + "marker.count", 0);
                    for (int m = 0; m < markerCount; m++) {
                        String markerKey = key + "marker." + m + ".";
                        double gelX = doubleValue(properties, markerKey + "gelX",
                                doubleValue(properties, markerKey + "x", 0.0));
                        double gelY = doubleValue(properties, markerKey + "gelY",
                                doubleValue(properties, markerKey + "y", 0.0));
                        cropMarkers.add(new CropMarker(
                                properties.getProperty(markerKey + "label", ""),
                                doubleValue(properties, markerKey + "cropY", 0.0),
                                doubleValue(properties, markerKey + "sourceX", gelX),
                                doubleValue(properties, markerKey + "sourceY", gelY),
                                gelX, gelY));
                    }
                    BandCrop band = new BandCrop(image, cropMarkers,
                            properties.getProperty(key + "label", "Protein"),
                            intValue(properties, key + "displayWidth", image.getWidth()),
                            sourcePath,
                            sourceWidth, sourceHeight, markerSet, mapping);
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
            updateActiveMarkerSetLabel();
            figureCanvas.refreshLayout();
            saveProject(false);
            return true;
        }

        private void loadLegacyMarkerSets(Properties properties,
                Map<String, KdaMarkerSet> setsById) {
            int cropCount = intValue(properties, "crop.count", 0);
            for (int i = 0; i < cropCount; i++) {
                String key = "crop." + i + ".";
                String id = properties.getProperty(key + "markerSet.id", "");
                if (id.length() == 0 || setsById.containsKey(id)) {
                    continue;
                }
                String type = properties.getProperty(key + "markerSet.sourceType", "Gel image");
                String sourcePath = properties.getProperty(key + "markerSet.sourcePath", "");
                int sourceWidth = intValue(properties, key + "markerSet.sourceWidth", 0);
                int sourceHeight = intValue(properties, key + "markerSet.sourceHeight", 0);
                if (sourceWidth <= 0 || sourceHeight <= 0) {
                    int[] dimensions = imageDimensions(sourcePath);
                    sourceWidth = dimensions[0];
                    sourceHeight = dimensions[1];
                }
                KdaMarkerSet set = new KdaMarkerSet(id, parseSourceType(type,
                        MarkerSourceType.GEL_IMAGE),
                        sourcePath, sourceWidth, sourceHeight);
                set.frozen = true;
                int count = intValue(properties, key + "markerSet.marker.count", 0);
                for (int m = 0; m < count; m++) {
                    String markerKey = key + "markerSet.marker." + m + ".";
                    set.markers.add(new KdaMarker(
                            doubleValue(properties, markerKey + "x", 0.0),
                            doubleValue(properties, markerKey + "y", 0.0),
                            properties.getProperty(markerKey + "label", "")));
                }
                markerSets.add(set);
                setsById.put(id, set);
            }
            if (setsById.isEmpty() && intValue(properties, "marker.count", 0) > 0) {
                String id = properties.getProperty("marker.activeSetId", "KDA-001");
                String sourcePath = markerPath != null ? markerPath : (gelPath == null ? "" : gelPath);
                KdaMarkerSet set = new KdaMarkerSet(id,
                        markerPath != null ? MarkerSourceType.MARKER_IMAGE : MarkerSourceType.GEL_IMAGE,
                        sourcePath, 0, 0);
                int count = intValue(properties, "marker.count", 0);
                for (int m = 0; m < count; m++) {
                    String markerKey = "marker." + m + ".";
                    set.markers.add(new KdaMarker(
                            doubleValue(properties, markerKey + "x", 0.0),
                            doubleValue(properties, markerKey + "y", 0.0),
                            properties.getProperty(markerKey + "label", "")));
                }
                markerSets.add(set);
                setsById.put(id, set);
            }
        }

        private MarkerMapping loadMarkerMapping(Properties properties, String key,
                KdaMarkerSet markerSet, int sourceWidth, int sourceHeight) {
            if (Boolean.parseBoolean(properties.getProperty(key + "mapping.present", "false"))) {
                return new MarkerMapping(
                        intValue(properties, key + "mapping.markerWidth", 0),
                        intValue(properties, key + "mapping.markerHeight", 0),
                        intValue(properties, key + "mapping.gelWidth", sourceWidth),
                        intValue(properties, key + "mapping.gelHeight", sourceHeight),
                        doubleValue(properties, key + "mapping.scaleX", 1.0),
                        doubleValue(properties, key + "mapping.scaleY", 1.0),
                        Boolean.parseBoolean(properties.getProperty(key + "mapping.dimensionsDiffer", "false")),
                        Boolean.parseBoolean(properties.getProperty(key + "mapping.aspectRatioMismatch", "false")));
            }
            if (markerSet == null) {
                return null;
            }
            double scaleX = doubleValue(properties, key + "markerSet.scaleX",
                    markerSet.sourceWidth > 0 ? sourceWidth / (double) markerSet.sourceWidth : 1.0);
            double scaleY = doubleValue(properties, key + "markerSet.scaleY",
                    markerSet.sourceHeight > 0 ? sourceHeight / (double) markerSet.sourceHeight : 1.0);
            return new MarkerMapping(markerSet.sourceWidth, markerSet.sourceHeight,
                    sourceWidth, sourceHeight, scaleX, scaleY,
                    markerSet.sourceWidth != sourceWidth || markerSet.sourceHeight != sourceHeight,
                    markerSet.sourceWidth > 0 && markerSet.sourceHeight > 0
                            && ((long) markerSet.sourceWidth) * sourceHeight
                            != ((long) sourceWidth) * markerSet.sourceHeight);
        }

        private int[] imageDimensions(String path) {
            if (path == null || path.length() == 0 || !new File(path).isFile()) {
                return new int[] {0, 0};
            }
            ImagePlus image = IJ.openImage(path);
            return image == null ? new int[] {0, 0}
                    : new int[] {image.getWidth(), image.getHeight()};
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

        private static String emptyToNull(String value) {
            return value == null || value.length() == 0 ? null : value;
        }

        private static MarkerSourceType parseSourceType(String value, MarkerSourceType fallback) {
            if ("MARKER_IMAGE".equals(value) || "kDa marker image".equalsIgnoreCase(value)) {
                return MarkerSourceType.MARKER_IMAGE;
            }
            if ("GEL_IMAGE".equals(value) || "Gel image".equalsIgnoreCase(value)) {
                return MarkerSourceType.GEL_IMAGE;
            }
            return fallback;
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

        private void openImage() {
            LoadedImage loaded = openRgbImage();
            if (loaded == null) {
                return;
            }
            cancelCropMode();
            if (kdaModeActive) {
                deactivateKdaMode();
            }
            clearOverlay(gelImp);
            gelImp = loaded.imagePlus;
            gelPath = loaded.path;
            markingSourceType = MarkerSourceType.GEL_IMAGE;
            startFreshMarkerSetOnNextMark = true;
            if (activeMarkerSet != null
                    && activeMarkerSet.sourceType != MarkerSourceType.MARKER_IMAGE) {
                activeMarkerSet = null;
            }
            showImageRightHalf(gelImp);
            warnAboutMarkerMapping(activeMarkerSet);
            redrawKdaOverlays();
            activateGelImage();
            setCropSelectionTool();
            updateActiveMarkerSetLabel();
            setStatus(activeMarkerSet == null
                    ? "Gel loaded. Click Mark kDa Bands to start a new marker set on this Gel."
                    : "Gel loaded. " + activeMarkerSet.id
                            + " from the kDa marker image is applied. Click Mark to start "
                            + "a new set directly on this Gel.");
            saveProject(false);
        }

        private void openMarkerImage() {
            LoadedImage loaded = openRgbImage();
            if (loaded == null) {
                return;
            }
            cancelCropMode();
            if (kdaModeActive) {
                deactivateKdaMode();
            }
            clearOverlay(markerImp);
            markerImp = loaded.imagePlus;
            markerPath = loaded.path;
            markingSourceType = MarkerSourceType.MARKER_IMAGE;
            startFreshMarkerSetOnNextMark = true;
            activeMarkerSet = null;
            showImageRightHalf(markerImp);
            redrawKdaOverlays();
            setCropSelectionTool();
            updateActiveMarkerSetLabel();
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

        private LoadedImage openRgbImage() {
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
            String path;
            try {
                path = chosen.getCanonicalPath();
            } catch (Exception ignored) {
                path = chosen.getAbsolutePath();
            }
            return new LoadedImage(imp, path);
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
            if (markingSourceImage() == null) {
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
            final ImagePlus source = markingSourceImage();
            if (source == null || source.getCanvas() == null) {
                return;
            }
            if (startFreshMarkerSetOnNextMark
                    || activeMarkerSet == null
                    || !activeMarkerSet.matchesSource(
                            markingSourceType, markingSourcePath(), source.getWidth(), source.getHeight())) {
                activeMarkerSet = createMarkerSetForCurrentSource();
                startFreshMarkerSetOnNextMark = false;
                warnAboutMarkerMapping(activeMarkerSet);
                redrawKdaOverlays();
                updateActiveMarkerSetLabel();
            }
            kdaModeActive = true;
            markButton.setText("Stop Marking kDa");
            markButton.setBackground(new Color(255, 180, 0));
            setStatus("kDa marking active on the " + markingSourceType.displayName
                    + ". Current set: " + activeMarkerSet.id + ".");
            IJ.setTool("point");

            final ImageCanvas canvas = source.getCanvas();
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
            KdaMarkerSet markerSet = editableMarkerSetForCurrentSource();
            startFreshMarkerSetOnNextMark = false;
            markerSet.markers.add(new KdaMarker(x, y, value));
            warnAboutMarkerMapping(markerSet);
            redrawKdaOverlays();
            updateActiveMarkerSetLabel();
            setStatus("kDa marking active. " + markerSet.markers.size()
                    + " marker(s) saved in " + markerSet.id + ".");
            saveProject(false);
        }

        private void toggleSourceKdaLabels() {
            showSourceKdaLabels = !showSourceKdaLabels;
            sourceKdaLabelsButton.setText(showSourceKdaLabels ? "Hide kDa Labels" : "Show kDa Labels");
            redrawKdaOverlays();
            redrawAnnotatedMarkerImages();
            setStatus(showSourceKdaLabels
                    ? "kDa labels are visible on the loaded images."
                    : "kDa labels are hidden on the loaded images; marker Xs remain visible.");
        }

        private void redrawKdaOverlays() {
            clearOverlay(markerImp);
            clearOverlay(gelImp);
            if (activeMarkerSet == null || activeMarkerSet.markers.isEmpty()) {
                return;
            }
            if (activeMarkerSet.sourceType == MarkerSourceType.MARKER_IMAGE) {
                if (markerImp != null && samePath(markerPath, activeMarkerSet.sourcePath)) {
                    drawKdaOverlay(markerImp, activeMarkerSet, false);
                }
                if (gelImp != null) {
                    drawKdaOverlay(gelImp, activeMarkerSet, true);
                }
            } else if (gelImp != null && samePath(gelPath, activeMarkerSet.sourcePath)) {
                drawKdaOverlay(gelImp, activeMarkerSet, false);
            }
        }

        private void drawKdaOverlay(ImagePlus image, KdaMarkerSet markerSet,
                boolean useGelCoordinates) {
            double scaleX = 1.0;
            double scaleY = 1.0;
            if (useGelCoordinates && gelImp != null) {
                scaleX = gelImp.getWidth() / (double) markerSet.sourceWidth;
                scaleY = gelImp.getHeight() / (double) markerSet.sourceHeight;
            }
            drawKdaOverlay(image, markerSet, scaleX, scaleY);
        }

        private void drawKdaOverlay(ImagePlus image, KdaMarkerSet markerSet,
                double scaleX, double scaleY) {
            if (image == null || markerSet == null || markerSet.markers.isEmpty()) {
                clearOverlay(image);
                return;
            }
            Overlay overlay = new Overlay();
            for (KdaMarker marker : markerSet.markers) {
                double x = marker.xAbs * scaleX;
                double y = marker.yAbs * scaleY;
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
            image.setOverlay(overlay);
            image.updateAndDraw();
        }

        private void redrawAnnotatedMarkerImages() {
            for (AnnotatedMarkerImage annotated : annotatedMarkerImages) {
                drawKdaOverlay(annotated.imagePlus, annotated.markerSet,
                        annotated.scaleX, annotated.scaleY);
            }
        }

        private ImagePlus markingSourceImage() {
            if (markingSourceType == MarkerSourceType.MARKER_IMAGE) {
                return markerImp;
            }
            if (markingSourceType == MarkerSourceType.GEL_IMAGE) {
                return gelImp;
            }
            return markerImp != null ? markerImp : gelImp;
        }

        private String markingSourcePath() {
            return markingSourceType == MarkerSourceType.MARKER_IMAGE ? markerPath : gelPath;
        }

        private KdaMarkerSet createMarkerSetForCurrentSource() {
            ImagePlus source = markingSourceImage();
            if (source == null || markingSourceType == null) {
                return null;
            }
            KdaMarkerSet markerSet = new KdaMarkerSet(nextMarkerSetId(), markingSourceType,
                    markingSourcePath(), source.getWidth(), source.getHeight());
            markerSets.add(markerSet);
            return markerSet;
        }

        private KdaMarkerSet editableMarkerSetForCurrentSource() {
            ImagePlus source = markingSourceImage();
            if (activeMarkerSet == null
                    || !activeMarkerSet.matchesSource(markingSourceType, markingSourcePath(),
                            source.getWidth(), source.getHeight())) {
                activeMarkerSet = createMarkerSetForCurrentSource();
                startFreshMarkerSetOnNextMark = false;
            } else if (activeMarkerSet.frozen) {
                KdaMarkerSet copy = activeMarkerSet.editableCopy(nextMarkerSetId());
                markerSets.add(copy);
                activeMarkerSet = copy;
            }
            return activeMarkerSet;
        }

        private String nextMarkerSetId() {
            return String.format(Locale.US, "KDA-%03d", Integer.valueOf(nextMarkerSetNumber++));
        }

        private void updateActiveMarkerSetLabel() {
            if (activeMarkerSet == null) {
                activeMarkerSetLabel.setText("Active markers: none");
                activeMarkerSetLabel.setToolTipText(null);
                return;
            }
            activeMarkerSetLabel.setText("Active: " + activeMarkerSet.id
                    + " (" + activeMarkerSet.sourceType.shortName + ")");
            activeMarkerSetLabel.setToolTipText(activeMarkerSet.sourcePath);
        }

        private void clearOverlay(ImagePlus imp) {
            if (imp != null) {
                imp.setOverlay(null);
                imp.updateAndDraw();
            }
        }

        private void undoLastKda() {
            if (activeMarkerSet == null || activeMarkerSet.markers.isEmpty()) {
                return;
            }
            if (activeMarkerSet.frozen) {
                KdaMarkerSet copy = activeMarkerSet.editableCopy(nextMarkerSetId());
                markerSets.add(copy);
                activeMarkerSet = copy;
            }
            activeMarkerSet.markers.remove(activeMarkerSet.markers.size() - 1);
            redrawKdaOverlays();
            updateActiveMarkerSetLabel();
            setStatus("Last marker removed from " + activeMarkerSet.id + ".");
            saveProject(false);
        }

        private void clearAllKda() {
            activeMarkerSet = null;
            startFreshMarkerSetOnNextMark = true;
            redrawKdaOverlays();
            updateActiveMarkerSetLabel();
            if (kdaModeActive) {
                setStatus("Markers cleared. The next marker starts a new set on the "
                        + markingSourceType.displayName + ".");
            } else {
                setStatus("Markers cleared. Click Mark kDa Bands to start a new set.");
            }
            saveProject(false);
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

            KdaMarkerSet cropMarkerSet = markerSetApplicableToCurrentGel();
            MarkerMapping markerMapping = markerMappingForCurrentGel(cropMarkerSet);
            warnAboutMarkerMapping(cropMarkerSet);
            List<CropMarker> localMarkers = new ArrayList<CropMarker>();
            if (cropMarkerSet != null) {
                for (KdaMarker marker : cropMarkerSet.markers) {
                    Point2D markerOnGel = markerInGelCoordinates(marker, cropMarkerSet);
                    double yInCrop = markerYInCrop(
                            markerOnGel.x, markerOnGel.y, crop.x, crop.y, crop.angleDeg);
                    if (yInCrop >= -0.5 && yInCrop <= crop.height + 0.5) {
                        localMarkers.add(new CropMarker(marker.label, yInCrop,
                                marker.xAbs, marker.yAbs, markerOnGel.x, markerOnGel.y));
                    }
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
            BandCrop band = new BandCrop(image, localMarkers, name.trim(), displayWidth,
                    gelPath, gelImp.getWidth(), gelImp.getHeight(), cropMarkerSet, markerMapping);
            band.cropX = crop.x;
            band.cropY = crop.y;
            band.cropWidth = crop.width;
            band.cropHeight = crop.height;
            band.cropAngleDeg = crop.angleDeg;
            if (cropMarkerSet != null) {
                cropMarkerSet.frozen = true;
            }
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

            return cropFromGeometry(imp, x, y, width, height, Math.toDegrees(angle));
        }

        private CropResult cropFromGeometry(ImagePlus imp, double x, double y,
                int width, int height, double angleDeg) {
            if (imp == null || width < 2 || height < 2) {
                return null;
            }
            double angle = Math.toRadians(angleDeg);
            ImagePlus cropped;
            if (Math.abs(angle) < 0.0001) {
                Roi oldRoi = imp.getRoi();
                imp.setRoi((int) Math.round(x), (int) Math.round(y), width, height);
                cropped = imp.crop();
                imp.setRoi(oldRoi);
                return new CropResult(cropped, x, y, width, height, angleDeg);
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
            return new CropResult(cropped, x, y, width, height, angleDeg);
        }

        private KdaMarkerSet markerSetApplicableToCurrentGel() {
            if (activeMarkerSet == null || gelImp == null) {
                return null;
            }
            if (activeMarkerSet.sourceType == MarkerSourceType.MARKER_IMAGE
                    || samePath(activeMarkerSet.sourcePath, gelPath)) {
                return activeMarkerSet;
            }
            return null;
        }

        private Point2D markerInGelCoordinates(KdaMarker marker, KdaMarkerSet markerSet) {
            if (gelImp == null || markerSet == null
                    || markerSet.sourceType == MarkerSourceType.GEL_IMAGE) {
                return new Point2D(marker.xAbs, marker.yAbs);
            }
            double scaleX = gelImp.getWidth() / (double) markerSet.sourceWidth;
            double scaleY = gelImp.getHeight() / (double) markerSet.sourceHeight;
            return new Point2D(marker.xAbs * scaleX, marker.yAbs * scaleY);
        }

        private MarkerMapping markerMappingForCurrentGel(KdaMarkerSet markerSet) {
            if (markerSet == null || gelImp == null) {
                return null;
            }
            double scaleX = gelImp.getWidth() / (double) markerSet.sourceWidth;
            double scaleY = gelImp.getHeight() / (double) markerSet.sourceHeight;
            boolean dimensionsDiffer = markerSet.sourceWidth != gelImp.getWidth()
                    || markerSet.sourceHeight != gelImp.getHeight();
            boolean aspectRatioMismatch = ((long) markerSet.sourceWidth) * gelImp.getHeight()
                    != ((long) gelImp.getWidth()) * markerSet.sourceHeight;
            return new MarkerMapping(markerSet.sourceWidth, markerSet.sourceHeight,
                    gelImp.getWidth(), gelImp.getHeight(), scaleX, scaleY,
                    dimensionsDiffer, aspectRatioMismatch);
        }

        private void warnAboutMarkerMapping(KdaMarkerSet markerSet) {
            if (markerSet == null || markerSet.markers.isEmpty() || gelImp == null
                    || markerSet.sourceType != MarkerSourceType.MARKER_IMAGE) {
                return;
            }
            MarkerMapping mapping = markerMappingForCurrentGel(markerSet);
            if (mapping == null || !mapping.dimensionsDiffer) {
                return;
            }
            String warningKey = markerSet.id + "|" + gelPath + "|"
                    + mapping.gelWidth + "x" + mapping.gelHeight;
            if (!shownMappingWarnings.add(warningKey)) {
                return;
            }
            StringBuilder message = new StringBuilder();
            message.append("The kDa marker image is ")
                    .append(mapping.markerWidth).append(" x ").append(mapping.markerHeight)
                    .append(" pixels, while the Gel is ")
                    .append(mapping.gelWidth).append(" x ").append(mapping.gelHeight)
                    .append(" pixels.\n\n");
            if (mapping.aspectRatioMismatch) {
                message.append("Their width-to-height ratios are different. Marker coordinates ")
                        .append("will be scaled independently in X and Y, and affected crops ")
                        .append("will contain a warning in the coordinate log.");
            } else {
                message.append("Their aspect ratios match. Marker coordinates will be ")
                        .append("scaled proportionally to the Gel dimensions.");
            }
            JOptionPane.showMessageDialog(frame, message.toString(),
                    mapping.aspectRatioMismatch
                            ? "kDa Aspect Ratio Warning" : "kDa Image Size Warning",
                    JOptionPane.WARNING_MESSAGE);
        }

        private static boolean samePath(String first, String second) {
            return first != null && second != null && first.equalsIgnoreCase(second);
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

        private void showCoordinateLog() {
            final JDialog dialog = new JDialog(frame, "GelAnno Coordinate Log", false);
            dialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
            dialog.setLayout(new BorderLayout(8, 8));

            final JTextArea textArea = new JTextArea(buildCoordinateLog(), 34, 92);
            textArea.setEditable(false);
            textArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
            textArea.setLineWrap(false);
            textArea.setCaretPosition(0);
            dialog.add(new JScrollPane(textArea), BorderLayout.CENTER);

            JPanel buttons = new JPanel(new FlowLayout(FlowLayout.RIGHT));
            JButton refresh = new JButton("Refresh");
            refresh.addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent event) {
                    textArea.setText(buildCoordinateLog());
                    textArea.setCaretPosition(0);
                }
            });
            buttons.add(refresh);

            JButton copy = new JButton("Copy");
            copy.addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent event) {
                    Toolkit.getDefaultToolkit().getSystemClipboard()
                            .setContents(new StringSelection(textArea.getText()), null);
                    setStatus("Coordinate log copied to the clipboard.");
                }
            });
            buttons.add(copy);

            JButton save = new JButton("Save Log...");
            save.addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent event) {
                    saveCoordinateLog(textArea.getText());
                }
            });
            buttons.add(save);

            JButton close = new JButton("Close");
            close.addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent event) {
                    dialog.dispose();
                }
            });
            buttons.add(close);
            dialog.add(buttons, BorderLayout.SOUTH);

            dialog.setSize(860, 650);
            dialog.setLocationRelativeTo(frame);
            dialog.setVisible(true);
        }

        private void showReconstructionLogDialog() {
            final JDialog dialog = new JDialog(frame, "Reconstruct from Coordinate Log", true);
            dialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
            dialog.setLayout(new BorderLayout(8, 8));

            final JTextArea textArea = new JTextArea(34, 92);
            textArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
            textArea.setLineWrap(false);
            dialog.add(new JScrollPane(textArea), BorderLayout.CENTER);

            JPanel buttons = new JPanel(new FlowLayout(FlowLayout.RIGHT));
            JButton load = new JButton("Load Log...");
            load.addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent event) {
                    JFileChooser chooser = new JFileChooser();
                    chooser.setDialogTitle("Load Coordinate Log");
                    chooser.setFileFilter(new FileNameExtensionFilter(
                            "Coordinate logs (TXT, LOG)", "txt", "log"));
                    if (lastDir != null) {
                        chooser.setCurrentDirectory(lastDir);
                    }
                    if (chooser.showOpenDialog(dialog) != JFileChooser.APPROVE_OPTION) {
                        return;
                    }
                    File file = chooser.getSelectedFile();
                    try {
                        byte[] bytes = Files.readAllBytes(file.toPath());
                        textArea.setText(new String(bytes, StandardCharsets.UTF_8));
                        textArea.setCaretPosition(0);
                        lastDir = file.getParentFile();
                    } catch (Exception ex) {
                        JOptionPane.showMessageDialog(dialog,
                                "Could not load the coordinate log.\n"
                                        + ex.getClass().getSimpleName() + ": " + ex.getMessage(),
                                "Load Coordinate Log", JOptionPane.ERROR_MESSAGE);
                    }
                }
            });
            buttons.add(load);

            JButton reconstruct = new JButton("Reconstruct");
            reconstruct.addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent event) {
                    ParsedCoordinateLog parsed;
                    try {
                        parsed = parseCoordinateLog(textArea.getText());
                    } catch (IllegalArgumentException ex) {
                        JOptionPane.showMessageDialog(dialog, ex.getMessage(),
                                "Invalid Coordinate Log", JOptionPane.ERROR_MESSAGE);
                        return;
                    }
                    dialog.dispose();
                    reconstructFromLog(parsed);
                }
            });
            buttons.add(reconstruct);

            JButton cancel = new JButton("Cancel");
            cancel.addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent event) {
                    dialog.dispose();
                }
            });
            buttons.add(cancel);
            dialog.add(buttons, BorderLayout.SOUTH);

            dialog.setSize(860, 650);
            dialog.setLocationRelativeTo(frame);
            dialog.setVisible(true);
        }

        private ParsedCoordinateLog parseCoordinateLog(String text) {
            if (text == null || text.trim().length() == 0) {
                throw new IllegalArgumentException("Paste a coordinate log or load one from a file.");
            }
            String normalized = text.replace("\r\n", "\n").replace('\r', '\n');
            String[] lines = normalized.split("\n", -1);
            if (lines.length == 0 || !("GelAnno Coordinate Log".equals(lines[0].trim())
                    || "WB Tool Coordinate Log".equals(lines[0].trim()))) {
                throw new IllegalArgumentException(
                        "This does not begin with a GelAnno Coordinate Log header.");
            }

            ParsedCoordinateLog parsed = new ParsedCoordinateLog();
            int section = 0;
            LoggedMarkerSet currentSet = null;
            LoggedCrop currentCrop = null;
            boolean inUsedMarkers = false;

            for (int index = 1; index < lines.length; index++) {
                String raw = lines[index];
                String line = raw.trim();
                int lineNumber = index + 1;
                if (line.length() == 0) {
                    continue;
                }
                if (line.startsWith("Log format version:")) {
                    parsed.formatVersion = parseInteger(
                            valueAfter(line, "Log format version:"), lineNumber, "log format version");
                    continue;
                }
                if (line.startsWith("Plugin version:")) {
                    parsed.pluginVersion = valueAfter(line, "Plugin version:");
                    continue;
                }
                if (line.startsWith("Figure name:")) {
                    parsed.figureName = unescapeLogValue(
                            valueAfter(line, "Figure name:"), parsed.formatVersion);
                    continue;
                }
                if ("Global kDa marker sets:".equals(line)) {
                    section = 1;
                    currentSet = null;
                    continue;
                }
                if ("Crops in figure:".equals(line)) {
                    section = 2;
                    currentSet = null;
                    continue;
                }

                if (section == 1) {
                    if (!startsWithWhitespace(raw) && line.endsWith(":")) {
                        String id = line.substring(0, line.length() - 1).trim();
                        if (id.length() == 0 || "none".equalsIgnoreCase(id)) {
                            continue;
                        }
                        currentSet = new LoggedMarkerSet(id);
                        parsed.markerSets.add(currentSet);
                        continue;
                    }
                    if (currentSet == null) {
                        continue;
                    }
                    if (line.startsWith("Source type:")) {
                        String type = valueAfter(line, "Source type:");
                        if ("kDa marker image".equalsIgnoreCase(type)) {
                            currentSet.sourceType = MarkerSourceType.MARKER_IMAGE;
                        } else if ("Gel image".equalsIgnoreCase(type)) {
                            currentSet.sourceType = MarkerSourceType.GEL_IMAGE;
                        } else {
                            throw parseError(lineNumber, "Unknown marker source type: " + type);
                        }
                    } else if (line.startsWith("Source image:")) {
                        currentSet.sourcePath = unescapeLogValue(
                                valueAfter(line, "Source image:"), parsed.formatVersion);
                    } else if (line.startsWith("Source dimensions:")) {
                        int[] dimensions = parseDimensions(
                                valueAfter(line, "Source dimensions:"), lineNumber);
                        currentSet.sourceWidth = dimensions[0];
                        currentSet.sourceHeight = dimensions[1];
                    } else if (isNumberedEntry(line) && line.contains(", x_abs = ")
                            && line.contains(", y_abs = ")) {
                        currentSet.markers.add(parseLoggedMarker(
                                line, lineNumber, parsed.formatVersion));
                    }
                    continue;
                }

                if (section == 2) {
                    if (!startsWithWhitespace(raw) && line.startsWith("Band ")) {
                        int colon = line.indexOf(':');
                        if (colon < 0) {
                            throw parseError(lineNumber, "Band entry has no name separator.");
                        }
                        currentCrop = new LoggedCrop();
                        currentCrop.name = unescapeLogValue(
                                line.substring(colon + 1).trim(), parsed.formatVersion);
                        parsed.crops.add(currentCrop);
                        inUsedMarkers = false;
                        continue;
                    }
                    if (currentCrop == null) {
                        continue;
                    }
                    if ("Used kDa markers:".equals(line)) {
                        inUsedMarkers = true;
                    } else if (!inUsedMarkers && line.startsWith("Source image:")) {
                        currentCrop.sourcePath = unescapeLogValue(
                                valueAfter(line, "Source image:"), parsed.formatVersion);
                    } else if (!inUsedMarkers && line.startsWith("Source dimensions:")) {
                        int[] dimensions = parseDimensions(
                                valueAfter(line, "Source dimensions:"), lineNumber);
                        currentCrop.sourceWidth = dimensions[0];
                        currentCrop.sourceHeight = dimensions[1];
                    } else if (line.startsWith("Crop origin:")) {
                        double[] pair = parseNamedPair(valueAfter(line, "Crop origin:"),
                                "x", "y", lineNumber);
                        currentCrop.cropX = pair[0];
                        currentCrop.cropY = pair[1];
                        currentCrop.hasOrigin = true;
                    } else if (line.startsWith("Crop size:")) {
                        double[] pair = parseNamedPair(valueAfter(line, "Crop size:"),
                                "width", "height", lineNumber);
                        currentCrop.cropWidth = (int) Math.round(pair[0]);
                        currentCrop.cropHeight = (int) Math.round(pair[1]);
                    } else if (line.startsWith("Crop angle:")) {
                        String value = valueAfter(line, "Crop angle:");
                        int degrees = value.indexOf(" degrees");
                        if (degrees >= 0) {
                            value = value.substring(0, degrees).trim();
                        }
                        currentCrop.cropAngleDeg = parseDouble(
                                value, lineNumber, "crop angle");
                    } else if (inUsedMarkers && line.startsWith("Marker set:")) {
                        String markerSetId = valueAfter(line, "Marker set:");
                        currentCrop.markerSetId = "none".equalsIgnoreCase(markerSetId)
                                ? null : markerSetId;
                    } else if (inUsedMarkers && isNumberedEntry(line)
                            && line.contains(", y_in_crop = ")) {
                        currentCrop.markers.add(parseLoggedCropMarker(
                                line, lineNumber, parsed.formatVersion));
                    }
                }
            }

            validateParsedCoordinateLog(parsed);
            return parsed;
        }

        private void validateParsedCoordinateLog(ParsedCoordinateLog parsed) {
            if (parsed.formatVersion < 0) {
                throw new IllegalArgumentException("Log format version cannot be negative.");
            }
            if (parsed.formatVersion > LOG_FORMAT_VERSION) {
                throw new IllegalArgumentException("Log format version " + parsed.formatVersion
                        + " is newer than this plugin supports (version "
                        + LOG_FORMAT_VERSION + ").");
            }
            Map<String, LoggedMarkerSet> markerSetsById =
                    new LinkedHashMap<String, LoggedMarkerSet>();
            for (LoggedMarkerSet markerSet : parsed.markerSets) {
                if (markerSet.sourceType == null || markerSet.sourcePath == null
                        || markerSet.sourceWidth <= 0
                        || markerSet.sourceHeight <= 0) {
                    throw new IllegalArgumentException("Marker set " + markerSet.id
                            + " is missing its source type, path, or dimensions.");
                }
                if (markerSetsById.containsKey(markerSet.id)) {
                    throw new IllegalArgumentException(
                            "The coordinate log contains duplicate marker set "
                                    + markerSet.id + ".");
                }
                markerSetsById.put(markerSet.id, markerSet);
            }
            if (parsed.crops.isEmpty()) {
                throw new IllegalArgumentException("The coordinate log contains no crops.");
            }
            int cropNumber = 1;
            for (LoggedCrop crop : parsed.crops) {
                if (crop.sourcePath == null || crop.sourceWidth <= 0 || crop.sourceHeight <= 0
                        || !crop.hasOrigin || crop.cropWidth <= 0 || crop.cropHeight <= 0) {
                    throw new IllegalArgumentException("Band " + cropNumber
                            + " is missing its source image, dimensions, or crop geometry.");
                }
                if (crop.markerSetId != null && !markerSetsById.containsKey(crop.markerSetId)) {
                    throw new IllegalArgumentException("Band " + cropNumber
                            + " refers to unknown marker set " + crop.markerSetId + ".");
                }
                if (crop.markerSetId == null && !crop.markers.isEmpty()) {
                    throw new IllegalArgumentException("Band " + cropNumber
                            + " contains marker coordinates but names no marker set.");
                }
                cropNumber++;
            }
            parsed.markerSetsById.putAll(markerSetsById);
        }

        private static LoggedMarker parseLoggedMarker(
                String line, int lineNumber, int formatVersion) {
            int labelStart = line.indexOf("label = ");
            int xStart = line.indexOf(", x_abs = ", labelStart);
            int yStart = line.indexOf(", y_abs = ", xStart);
            if (labelStart < 0 || xStart < 0 || yStart < 0) {
                throw parseError(lineNumber, "Invalid marker coordinate entry.");
            }
            String label = unescapeLogValue(
                    line.substring(labelStart + "label = ".length(), xStart).trim(),
                    formatVersion);
            double x = parseDouble(line.substring(xStart + ", x_abs = ".length(), yStart).trim(),
                    lineNumber, "marker x coordinate");
            double y = parseDouble(line.substring(yStart + ", y_abs = ".length()).trim(),
                    lineNumber, "marker y coordinate");
            return new LoggedMarker(label, x, y);
        }

        private static LoggedCropMarker parseLoggedCropMarker(
                String line, int lineNumber, int formatVersion) {
            int labelStart = line.indexOf("label = ");
            int sourceXStart = line.indexOf(", source_x_abs = ", labelStart);
            int sourceYStart = line.indexOf(", source_y_abs = ", sourceXStart);
            int gelXStart = line.indexOf(", gel_x_abs = ", sourceYStart);
            int gelYStart = line.indexOf(", gel_y_abs = ", gelXStart);
            int yInCropStart = line.lastIndexOf(", y_in_crop = ");
            if (labelStart < 0 || sourceXStart < 0 || sourceYStart < 0
                    || gelXStart < 0 || gelYStart < 0 || yInCropStart < 0) {
                throw parseError(lineNumber, "Invalid crop marker entry.");
            }
            String label = unescapeLogValue(
                    line.substring(labelStart + "label = ".length(), sourceXStart).trim(),
                    formatVersion);
            double sourceX = parseDouble(line.substring(
                    sourceXStart + ", source_x_abs = ".length(), sourceYStart).trim(),
                    lineNumber, "source marker x coordinate");
            double sourceY = parseDouble(line.substring(
                    sourceYStart + ", source_y_abs = ".length(), gelXStart).trim(),
                    lineNumber, "source marker y coordinate");
            double gelX = parseDouble(line.substring(
                    gelXStart + ", gel_x_abs = ".length(), gelYStart).trim(),
                    lineNumber, "Gel marker x coordinate");
            double gelY = parseDouble(line.substring(
                    gelYStart + ", gel_y_abs = ".length(), yInCropStart).trim(),
                    lineNumber, "Gel marker y coordinate");
            double yInCrop = parseDouble(
                    line.substring(yInCropStart + ", y_in_crop = ".length()).trim(),
                    lineNumber, "marker y_in_crop coordinate");
            return new LoggedCropMarker(label, sourceX, sourceY, gelX, gelY, yInCrop);
        }

        private static int[] parseDimensions(String value, int lineNumber) {
            String cleaned = value.replace(" pixels", "").trim();
            int separator = cleaned.indexOf(" x ");
            if (separator < 0) {
                throw parseError(lineNumber, "Invalid image dimensions.");
            }
            int width = parseInteger(cleaned.substring(0, separator).trim(),
                    lineNumber, "image width");
            int height = parseInteger(cleaned.substring(separator + 3).trim(),
                    lineNumber, "image height");
            return new int[] {width, height};
        }

        private static double[] parseNamedPair(String value, String firstName,
                String secondName, int lineNumber) {
            String firstPrefix = firstName + " = ";
            String secondPrefix = ", " + secondName + " = ";
            int firstStart = value.indexOf(firstPrefix);
            int secondStart = value.indexOf(secondPrefix, firstStart + firstPrefix.length());
            if (firstStart < 0 || secondStart < 0) {
                throw parseError(lineNumber, "Invalid " + firstName + "/" + secondName + " pair.");
            }
            String firstValue = value.substring(firstStart + firstPrefix.length(), secondStart).trim();
            String secondValue = value.substring(secondStart + secondPrefix.length())
                    .replace(" pixels", "").trim();
            return new double[] {
                parseDouble(firstValue, lineNumber, firstName),
                parseDouble(secondValue, lineNumber, secondName)
            };
        }

        private static String valueAfter(String line, String prefix) {
            return line.substring(prefix.length()).trim();
        }

        private static int parseInteger(String value, int lineNumber, String field) {
            try {
                return Integer.parseInt(value);
            } catch (NumberFormatException ex) {
                throw parseError(lineNumber, "Invalid " + field + ": " + value);
            }
        }

        private static double parseDouble(String value, int lineNumber, String field) {
            try {
                double parsed = Double.parseDouble(value);
                if (Double.isNaN(parsed) || Double.isInfinite(parsed)) {
                    throw parseError(lineNumber, "Invalid " + field + ": " + value);
                }
                return parsed;
            } catch (NumberFormatException ex) {
                throw parseError(lineNumber, "Invalid " + field + ": " + value);
            }
        }

        private static boolean startsWithWhitespace(String value) {
            return value.length() > 0 && Character.isWhitespace(value.charAt(0));
        }

        private static boolean isNumberedEntry(String value) {
            int dot = value.indexOf('.');
            if (dot <= 0) {
                return false;
            }
            for (int i = 0; i < dot; i++) {
                if (!Character.isDigit(value.charAt(i))) {
                    return false;
                }
            }
            return true;
        }

        private static IllegalArgumentException parseError(int lineNumber, String message) {
            return new IllegalArgumentException("Coordinate log line " + lineNumber + ": " + message);
        }

        private static String unescapeLogValue(String value, int formatVersion) {
            return value;
        }

        private void reconstructFromLog(ParsedCoordinateLog parsed) {
            LinkedHashMap<String, ReconstructionImageRequest> requests =
                    buildReconstructionImageRequests(parsed);
            for (ReconstructionImageRequest request : requests.values()) {
                if (!selectReconstructionImage(request)) {
                    setStatus("Reconstruction cancelled.");
                    return;
                }
            }

            Controller reconstructed = new Controller(
                    TITLE + " - Reconstructed from coordinate log");
            reconstructed.showFrame();
            reconstructed.figureTitleField.setText(parsed.figureName == null
                    || parsed.figureName.trim().length() == 0
                            ? "Reconstructed figure" : parsed.figureName.trim());

            Map<String, KdaMarkerSet> reconstructedSets =
                    new LinkedHashMap<String, KdaMarkerSet>();
            int highestMarkerSetNumber = 0;
            for (LoggedMarkerSet loggedSet : parsed.markerSets) {
                KdaMarkerSet markerSet = new KdaMarkerSet(loggedSet.id, loggedSet.sourceType,
                        loggedSet.sourcePath, loggedSet.sourceWidth, loggedSet.sourceHeight);
                for (LoggedMarker marker : loggedSet.markers) {
                    markerSet.markers.add(new KdaMarker(marker.xAbs, marker.yAbs, marker.label));
                }
                markerSet.frozen = true;
                reconstructed.markerSets.add(markerSet);
                reconstructedSets.put(markerSet.id, markerSet);
                highestMarkerSetNumber = Math.max(
                        highestMarkerSetNumber, markerSetNumber(markerSet.id));
            }
            reconstructed.nextMarkerSetNumber = highestMarkerSetNumber + 1;

            List<String> reconstructionWarnings = new ArrayList<String>();
            for (ReconstructionImageRequest request : requests.values()) {
                if (request.dimensionMismatch && request.loadedImage != null) {
                    reconstructionWarnings.add("Selected dimensions differ for "
                            + request.originalPath
                            + (request.aspectRatioMismatch
                                    ? "; the aspect ratios also differ." : "."));
                }
                if (request.conflictingLoggedDimensions) {
                    reconstructionWarnings.add("The log contains conflicting dimensions for "
                            + request.originalPath + ".");
                }
            }

            int bandNumber = 1;
            for (LoggedCrop loggedCrop : parsed.crops) {
                ReconstructionImageRequest request = requests.get(
                        reconstructionRequestKey(loggedCrop.sourcePath));
                if (request == null || request.loadedImage == null) {
                    JOptionPane.showMessageDialog(frame,
                            "Required Gel image is missing for Band " + bandNumber + ".",
                            "Reconstruction Failed", JOptionPane.ERROR_MESSAGE);
                    reconstructed.frame.dispose();
                    return;
                }
                ReconstructedGeometry geometry = scaleLoggedCropGeometry(
                        loggedCrop, request.loadedImage.imagePlus);
                CropResult crop = reconstructed.cropFromGeometry(
                        request.loadedImage.imagePlus, geometry.x, geometry.y,
                        geometry.width, geometry.height, geometry.angleDeg);
                if (crop == null) {
                    JOptionPane.showMessageDialog(frame,
                            "Could not reconstruct Band " + bandNumber
                                    + " from the selected Gel image.",
                            "Reconstruction Failed", JOptionPane.ERROR_MESSAGE);
                    reconstructed.frame.dispose();
                    return;
                }

                double localScaleY = crop.height / (double) loggedCrop.cropHeight;
                List<CropMarker> cropMarkers = new ArrayList<CropMarker>();
                for (LoggedCropMarker marker : loggedCrop.markers) {
                    cropMarkers.add(new CropMarker(marker.label,
                            marker.yInCrop * localScaleY,
                            marker.sourceXAbs, marker.sourceYAbs,
                            marker.gelXAbs, marker.gelYAbs));
                }
                Collections.sort(cropMarkers, new Comparator<CropMarker>() {
                    @Override
                    public int compare(CropMarker first, CropMarker second) {
                        return Double.compare(first.yInCrop, second.yInCrop);
                    }
                });

                BufferedImage image = crop.imagePlus.getProcessor()
                        .convertToRGB().getBufferedImage();
                int displayWidth = reconstructed.chooseInitialDisplayWidth(image.getWidth());
                KdaMarkerSet markerSet = loggedCrop.markerSetId == null
                        ? null : reconstructedSets.get(loggedCrop.markerSetId);
                MarkerMapping markerMapping = markerMappingForLoggedCrop(markerSet, loggedCrop);
                BandCrop band = new BandCrop(image, cropMarkers, loggedCrop.name, displayWidth,
                        loggedCrop.sourcePath, loggedCrop.sourceWidth, loggedCrop.sourceHeight,
                        markerSet, markerMapping);
                band.cropX = loggedCrop.cropX;
                band.cropY = loggedCrop.cropY;
                band.cropWidth = loggedCrop.cropWidth;
                band.cropHeight = loggedCrop.cropHeight;
                band.cropAngleDeg = loggedCrop.cropAngleDeg;
                reconstructed.bands.add(band);
                reconstructed.selectedBand = band;
                bandNumber++;
            }
            reconstructed.figureCanvas.refreshLayout();

            List<String> skippedMarkerSets = new ArrayList<String>();
            int annotatedIndex = 0;
            for (LoggedMarkerSet loggedSet : parsed.markerSets) {
                ReconstructionImageRequest request = requests.get(
                        reconstructionRequestKey(loggedSet.sourcePath));
                if (request == null || request.loadedImage == null) {
                    skippedMarkerSets.add(loggedSet.id);
                    continue;
                }
                KdaMarkerSet markerSet = reconstructedSets.get(loggedSet.id);
                reconstructed.openAnnotatedMarkerImage(
                        markerSet, request.loadedImage, annotatedIndex++);
            }

            String status = "Reconstructed " + reconstructed.bands.size()
                    + " crop(s) from coordinate log.";
            if (!skippedMarkerSets.isEmpty()) {
                status += " Marker sources not supplied: " + joinValues(skippedMarkerSets) + ".";
            }
            reconstructed.setStatus(status);
            reconstructed.saveProject(false);
            reconstructed.frame.toFront();

            if (!skippedMarkerSets.isEmpty() || !reconstructionWarnings.isEmpty()) {
                StringBuilder warning = new StringBuilder();
                warning.append("The figure was reconstructed with warnings.\n");
                if (!skippedMarkerSets.isEmpty()) {
                    warning.append("\nMarker source images were not supplied for: ")
                            .append(joinValues(skippedMarkerSets)).append(".");
                }
                for (String item : reconstructionWarnings) {
                    warning.append("\n").append(item);
                }
                JOptionPane.showMessageDialog(reconstructed.frame, warning.toString(),
                        "Reconstruction Warnings", JOptionPane.WARNING_MESSAGE);
            }
        }

        private LinkedHashMap<String, ReconstructionImageRequest>
                buildReconstructionImageRequests(ParsedCoordinateLog parsed) {
            LinkedHashMap<String, ReconstructionImageRequest> requests =
                    new LinkedHashMap<String, ReconstructionImageRequest>();
            int bandNumber = 1;
            for (LoggedCrop crop : parsed.crops) {
                ReconstructionImageRequest request = getOrCreateReconstructionRequest(
                        requests, crop.sourcePath, crop.sourceWidth, crop.sourceHeight);
                request.required = true;
                request.addRole("Gel for Band " + bandNumber + " (" + crop.name + ")");
                bandNumber++;
            }
            for (LoggedMarkerSet markerSet : parsed.markerSets) {
                ReconstructionImageRequest request = getOrCreateReconstructionRequest(
                        requests, markerSet.sourcePath,
                        markerSet.sourceWidth, markerSet.sourceHeight);
                request.addRole("Marker source for " + markerSet.id);
            }
            return requests;
        }

        private static ReconstructionImageRequest getOrCreateReconstructionRequest(
                LinkedHashMap<String, ReconstructionImageRequest> requests,
                String path, int width, int height) {
            String key = reconstructionRequestKey(path);
            ReconstructionImageRequest request = requests.get(key);
            if (request == null) {
                request = new ReconstructionImageRequest(path, width, height);
                requests.put(key, request);
            } else if (request.expectedWidth != width || request.expectedHeight != height) {
                request.conflictingLoggedDimensions = true;
            }
            return request;
        }

        private boolean selectReconstructionImage(ReconstructionImageRequest request) {
            while (true) {
                JFileChooser chooser = new JFileChooser();
                chooser.setDialogTitle(request.required
                        ? "Select Required Gel Image" : "Select Marker Source Image");
                chooser.setApproveButtonText("Use Image");
                chooser.setFileFilter(new FileNameExtensionFilter(
                        "Image files (TIFF, PNG, JPEG)", "tif", "tiff", "png", "jpg", "jpeg"));
                if (lastDir != null) {
                    chooser.setCurrentDirectory(lastDir);
                }

                JTextArea details = new JTextArea(reconstructionImageDetails(request), 9, 34);
                details.setEditable(false);
                details.setOpaque(false);
                details.setLineWrap(true);
                details.setWrapStyleWord(true);
                chooser.setAccessory(details);

                if (chooser.showOpenDialog(frame) != JFileChooser.APPROVE_OPTION) {
                    if (request.required) {
                        return false;
                    }
                    Object[] options = {"Skip Marker Source", "Choose Again", "Cancel Reconstruction"};
                    int choice = JOptionPane.showOptionDialog(frame,
                            "No image was selected for this optional marker source.",
                            "Marker Source Image", JOptionPane.DEFAULT_OPTION,
                            JOptionPane.QUESTION_MESSAGE, null, options, options[0]);
                    if (choice == 0) {
                        return true;
                    }
                    if (choice == 1) {
                        continue;
                    }
                    return false;
                }

                File selected = chooser.getSelectedFile();
                LoadedImage loaded = loadRgbImage(selected);
                if (loaded == null) {
                    continue;
                }
                lastDir = selected.getParentFile();
                if (lastDir != null) {
                    Prefs.set("wbtool.last_dir", lastDir.getAbsolutePath());
                }

                if (loaded.imagePlus.getWidth() != request.expectedWidth
                        || loaded.imagePlus.getHeight() != request.expectedHeight) {
                    boolean ratioMismatch = ((long) loaded.imagePlus.getWidth())
                            * request.expectedHeight
                            != ((long) request.expectedWidth) * loaded.imagePlus.getHeight();
                    StringBuilder warning = new StringBuilder();
                    warning.append("The log expects ")
                            .append(request.expectedWidth).append(" x ")
                            .append(request.expectedHeight).append(" pixels, but the selected image is ")
                            .append(loaded.imagePlus.getWidth()).append(" x ")
                            .append(loaded.imagePlus.getHeight()).append(" pixels.\n\n");
                    warning.append(ratioMismatch
                            ? "The aspect ratios differ, so this will not be an exact reconstruction."
                            : "The aspect ratios match and coordinates can be scaled proportionally.");
                    int choice = JOptionPane.showConfirmDialog(frame, warning.toString()
                                    + "\n\nUse this image anyway?",
                            "Reconstruction Image Size Warning",
                            JOptionPane.YES_NO_OPTION, JOptionPane.WARNING_MESSAGE);
                    if (choice != JOptionPane.YES_OPTION) {
                        continue;
                    }
                    request.dimensionMismatch = true;
                    request.aspectRatioMismatch = ratioMismatch;
                }
                request.loadedImage = loaded;
                return true;
            }
        }

        private LoadedImage loadRgbImage(File file) {
            ImagePlus imp = IJ.openImage(file.getAbsolutePath());
            if (imp == null) {
                JOptionPane.showMessageDialog(frame, "Could not open: " + file.getAbsolutePath(),
                        "Open Reconstruction Image", JOptionPane.ERROR_MESSAGE);
                return null;
            }
            if (imp.getType() != ImagePlus.COLOR_RGB) {
                new ImageConverter(imp).convertToRGB();
            }
            String path;
            try {
                path = file.getCanonicalPath();
            } catch (Exception ignored) {
                path = file.getAbsolutePath();
            }
            return new LoadedImage(imp, path);
        }

        private static String reconstructionImageDetails(ReconstructionImageRequest request) {
            StringBuilder details = new StringBuilder();
            details.append(request.required ? "Required Gel image" : "Optional marker source")
                    .append("\n\nExpected path:\n").append(request.originalPath)
                    .append("\n\nLogged dimensions: ")
                    .append(request.expectedWidth).append(" x ").append(request.expectedHeight)
                    .append(" pixels\n\nUsed as:\n");
            for (String role : request.roles) {
                details.append("- ").append(role).append("\n");
            }
            if (request.conflictingLoggedDimensions) {
                details.append("\nWarning: this path has conflicting dimensions in the log.");
            }
            return details.toString();
        }

        private static ReconstructedGeometry scaleLoggedCropGeometry(
                LoggedCrop crop, ImagePlus selectedImage) {
            double scaleX = selectedImage.getWidth() / (double) crop.sourceWidth;
            double scaleY = selectedImage.getHeight() / (double) crop.sourceHeight;
            double angle = Math.toRadians(crop.cropAngleDeg);

            Point2D topLeft = new Point2D(crop.cropX * scaleX, crop.cropY * scaleY);
            Point2D topRight = new Point2D(
                    (crop.cropX + crop.cropWidth * Math.cos(angle)) * scaleX,
                    (crop.cropY + crop.cropWidth * Math.sin(angle)) * scaleY);
            Point2D bottomLeft = new Point2D(
                    (crop.cropX - crop.cropHeight * Math.sin(angle)) * scaleX,
                    (crop.cropY + crop.cropHeight * Math.cos(angle)) * scaleY);

            int width = Math.max(2, (int) Math.round(distance(
                    topLeft.x, topLeft.y, topRight.x, topRight.y)));
            int height = Math.max(2, (int) Math.round(distance(
                    topLeft.x, topLeft.y, bottomLeft.x, bottomLeft.y)));
            double scaledAngle = Math.toDegrees(Math.atan2(
                    topRight.y - topLeft.y, topRight.x - topLeft.x));
            return new ReconstructedGeometry(
                    topLeft.x, topLeft.y, width, height, scaledAngle);
        }

        private static MarkerMapping markerMappingForLoggedCrop(
                KdaMarkerSet markerSet, LoggedCrop crop) {
            if (markerSet == null) {
                return null;
            }
            double scaleX = crop.sourceWidth / (double) markerSet.sourceWidth;
            double scaleY = crop.sourceHeight / (double) markerSet.sourceHeight;
            boolean dimensionsDiffer = markerSet.sourceWidth != crop.sourceWidth
                    || markerSet.sourceHeight != crop.sourceHeight;
            boolean ratioMismatch = ((long) markerSet.sourceWidth) * crop.sourceHeight
                    != ((long) crop.sourceWidth) * markerSet.sourceHeight;
            return new MarkerMapping(markerSet.sourceWidth, markerSet.sourceHeight,
                    crop.sourceWidth, crop.sourceHeight, scaleX, scaleY,
                    dimensionsDiffer, ratioMismatch);
        }

        private void openAnnotatedMarkerImage(KdaMarkerSet markerSet,
                LoadedImage loadedImage, int index) {
            if (markerSet == null || loadedImage == null) {
                return;
            }
            ImagePlus annotatedImage = new ImagePlus(
                    markerSet.id + " - marker source - " + new File(loadedImage.path).getName(),
                    loadedImage.imagePlus.getProcessor().duplicate());
            double scaleX = annotatedImage.getWidth() / (double) markerSet.sourceWidth;
            double scaleY = annotatedImage.getHeight() / (double) markerSet.sourceHeight;
            AnnotatedMarkerImage annotated = new AnnotatedMarkerImage(
                    annotatedImage, markerSet, scaleX, scaleY);
            annotatedMarkerImages.add(annotated);
            annotatedImage.show();
            Dimension screen = Toolkit.getDefaultToolkit().getScreenSize();
            if (annotatedImage.getWindow() != null) {
                int offset = (index % 8) * 24;
                annotatedImage.getWindow().setLocation(screen.width / 2 + offset, offset);
                annotatedImage.getWindow().setSize(
                        Math.max(320, screen.width / 2 - offset),
                        Math.max(280, screen.height - offset));
            }
            drawKdaOverlay(annotatedImage, markerSet, scaleX, scaleY);
        }

        private static String reconstructionRequestKey(String path) {
            if (path == null) {
                return "";
            }
            return File.separatorChar == '\\' ? path.toLowerCase(Locale.US) : path;
        }

        private static String joinValues(List<String> values) {
            StringBuilder joined = new StringBuilder();
            for (String value : values) {
                if (joined.length() > 0) {
                    joined.append(", ");
                }
                joined.append(value);
            }
            return joined.toString();
        }

        private static int markerSetNumber(String id) {
            if (id == null) {
                return 0;
            }
            int dash = id.lastIndexOf('-');
            if (dash < 0 || dash == id.length() - 1) {
                return 0;
            }
            try {
                return Integer.parseInt(id.substring(dash + 1));
            } catch (NumberFormatException ignored) {
                return 0;
            }
        }

        private void saveCoordinateLog(String text) {
            File path = chooseSavePath("Save Coordinate Log", "Text files", "txt");
            if (path == null) {
                return;
            }
            Writer writer = null;
            try {
                writer = new OutputStreamWriter(new FileOutputStream(path), StandardCharsets.UTF_8);
                writer.write(text);
                writer.close();
                setStatus("Coordinate log saved: " + path.getAbsolutePath());
            } catch (Exception ex) {
                try {
                    if (writer != null) {
                        writer.close();
                    }
                } catch (Exception ignored) {
                    // Preserve the original save error.
                }
                JOptionPane.showMessageDialog(frame,
                        "Could not save the coordinate log.\n"
                                + ex.getClass().getSimpleName() + ": " + ex.getMessage(),
                        "Save Coordinate Log", JOptionPane.ERROR_MESSAGE);
            }
        }

        private String buildCoordinateLog() {
            StringBuilder log = new StringBuilder();
            log.append("GelAnno Coordinate Log\n");
            log.append("Log format version: ").append(LOG_FORMAT_VERSION).append("\n");
            log.append("Plugin version: ").append(VERSION).append("\n");
            log.append("Figure name: ").append(logValue(figureTitle())).append("\n\n");
            log.append("Coordinate convention:\n");
            log.append("  Origin: top-left image pixel\n");
            log.append("  X direction: right\n");
            log.append("  Y direction: down\n");
            log.append("  Crop corners: top-left, top-right, bottom-right, bottom-left\n");
            log.append("  Angles: degrees clockwise in image coordinates\n\n");

            log.append("Global kDa marker sets:\n");
            boolean wroteMarkerSet = false;
            for (KdaMarkerSet markerSet : markerSets) {
                if (markerSet.markers.isEmpty() && !isMarkerSetUsed(markerSet)) {
                    continue;
                }
                wroteMarkerSet = true;
                log.append(markerSet.id).append(":\n");
                log.append("  Source type: ").append(markerSet.sourceType.displayName).append("\n");
                log.append("  Source image: ").append(logValue(markerSet.sourcePath)).append("\n");
                log.append("  Source dimensions: ").append(markerSet.sourceWidth).append(" x ")
                        .append(markerSet.sourceHeight).append(" pixels\n");
                log.append("  Markers:\n");
                if (markerSet.markers.isEmpty()) {
                    log.append("    none\n");
                } else {
                    int markerNumber = 1;
                    for (KdaMarker marker : markerSet.markers) {
                        log.append("    ").append(markerNumber++).append(". label = ")
                                .append(logValue(marker.label))
                                .append(", x_abs = ").append(formatCoordinate(marker.xAbs))
                                .append(", y_abs = ").append(formatCoordinate(marker.yAbs))
                                .append("\n");
                    }
                }
                log.append("\n");
            }
            if (!wroteMarkerSet) {
                log.append("  none\n\n");
            }

            log.append("Crops in figure:\n");
            if (bands.isEmpty()) {
                log.append("  none\n");
                return log.toString();
            }

            int bandNumber = 1;
            for (BandCrop band : bands) {
                log.append("Band ").append(bandNumber++).append(": ")
                        .append(logValue(band.label)).append("\n");
                log.append("  Source image: ").append(logValue(band.sourcePath)).append("\n");
                log.append("  Source dimensions: ").append(band.sourceWidth).append(" x ")
                        .append(band.sourceHeight).append(" pixels\n");
                log.append("  Crop origin: x = ").append(formatCoordinate(band.cropX))
                        .append(", y = ").append(formatCoordinate(band.cropY)).append("\n");
                log.append("  Crop size: width = ").append(band.cropWidth)
                        .append(", height = ").append(band.cropHeight).append(" pixels\n");
                log.append("  Crop angle: ").append(formatCoordinate(band.cropAngleDeg))
                        .append(" degrees\n");
                Point2D[] corners = cropCorners(band);
                log.append("  Crop corners:\n");
                appendCorner(log, "top-left", corners[0]);
                appendCorner(log, "top-right", corners[1]);
                appendCorner(log, "bottom-right", corners[2]);
                appendCorner(log, "bottom-left", corners[3]);

                log.append("  Used kDa markers:\n");
                if (band.markerSet == null) {
                    log.append("    Marker set: none\n");
                } else {
                    log.append("    Marker set: ").append(band.markerSet.id).append("\n");
                    log.append("    Marker source image: ")
                            .append(logValue(band.markerSet.sourcePath)).append("\n");
                    if (band.markerMapping != null) {
                        MarkerMapping mapping = band.markerMapping;
                        log.append("    Marker source dimensions: ")
                                .append(mapping.markerWidth).append(" x ")
                                .append(mapping.markerHeight).append(" pixels\n");
                        log.append("    Gel dimensions: ").append(mapping.gelWidth).append(" x ")
                                .append(mapping.gelHeight).append(" pixels\n");
                        log.append("    Coordinate scale: x = ")
                                .append(formatCoordinate(mapping.scaleX))
                                .append(", y = ").append(formatCoordinate(mapping.scaleY)).append("\n");
                        if (mapping.aspectRatioMismatch) {
                            log.append("    WARNING: Marker source and Gel have different ")
                                    .append("width-to-height ratios.\n");
                        } else if (mapping.dimensionsDiffer) {
                            log.append("    Note: Image dimensions differ, but their aspect ratios match.\n");
                        }
                    }
                    if (band.markers.isEmpty()) {
                        log.append("    No markers from this set fell within the crop.\n");
                    } else {
                        int usedNumber = 1;
                        for (CropMarker marker : band.markers) {
                            log.append("    ").append(usedNumber++).append(". label = ")
                                    .append(logValue(marker.label))
                                    .append(", source_x_abs = ")
                                    .append(formatCoordinate(marker.sourceXAbs))
                                    .append(", source_y_abs = ")
                                    .append(formatCoordinate(marker.sourceYAbs))
                                    .append(", gel_x_abs = ")
                                    .append(formatCoordinate(marker.gelXAbs))
                                    .append(", gel_y_abs = ")
                                    .append(formatCoordinate(marker.gelYAbs))
                                    .append(", y_in_crop = ")
                                    .append(formatCoordinate(marker.yInCrop)).append("\n");
                        }
                    }
                }
                log.append("\n");
            }
            return log.toString();
        }

        private boolean isMarkerSetUsed(KdaMarkerSet markerSet) {
            for (BandCrop band : bands) {
                if (band.markerSet == markerSet) {
                    return true;
                }
            }
            return false;
        }

        private static Point2D[] cropCorners(BandCrop band) {
            double angle = Math.toRadians(band.cropAngleDeg);
            double cos = Math.cos(angle);
            double sin = Math.sin(angle);
            Point2D topLeft = new Point2D(band.cropX, band.cropY);
            Point2D topRight = new Point2D(
                    band.cropX + band.cropWidth * cos,
                    band.cropY + band.cropWidth * sin);
            Point2D bottomLeft = new Point2D(
                    band.cropX - band.cropHeight * sin,
                    band.cropY + band.cropHeight * cos);
            Point2D bottomRight = new Point2D(
                    topRight.x + bottomLeft.x - topLeft.x,
                    topRight.y + bottomLeft.y - topLeft.y);
            return new Point2D[] {topLeft, topRight, bottomRight, bottomLeft};
        }

        private static void appendCorner(StringBuilder log, String name, Point2D point) {
            log.append("    ").append(name).append(": x = ")
                    .append(formatCoordinate(point.x)).append(", y = ")
                    .append(formatCoordinate(point.y)).append("\n");
        }

        private static String formatCoordinate(double value) {
            return String.format(Locale.US, "%.6f", Double.valueOf(value));
        }

        private static String logValue(String value) {
            if (value == null) {
                return "unknown";
            }
            return value.replace("\r", "\\r").replace("\n", "\\n");
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

    private static final class ParsedCoordinateLog {
        int formatVersion;
        String pluginVersion;
        String figureName;
        final List<LoggedMarkerSet> markerSets = new ArrayList<LoggedMarkerSet>();
        final Map<String, LoggedMarkerSet> markerSetsById =
                new LinkedHashMap<String, LoggedMarkerSet>();
        final List<LoggedCrop> crops = new ArrayList<LoggedCrop>();
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

    private static final class LoggedMarkerSet {
        final String id;
        MarkerSourceType sourceType;
        String sourcePath;
        int sourceWidth;
        int sourceHeight;
        final List<LoggedMarker> markers = new ArrayList<LoggedMarker>();

        LoggedMarkerSet(String id) {
            this.id = id;
        }
    }

    private static final class LoggedMarker {
        final String label;
        final double xAbs;
        final double yAbs;

        LoggedMarker(String label, double xAbs, double yAbs) {
            this.label = label;
            this.xAbs = xAbs;
            this.yAbs = yAbs;
        }
    }

    private static final class LoggedCrop {
        String name;
        String sourcePath;
        int sourceWidth;
        int sourceHeight;
        double cropX;
        double cropY;
        int cropWidth;
        int cropHeight;
        double cropAngleDeg;
        boolean hasOrigin;
        String markerSetId;
        final List<LoggedCropMarker> markers = new ArrayList<LoggedCropMarker>();
    }

    private static final class LoggedCropMarker {
        final String label;
        final double sourceXAbs;
        final double sourceYAbs;
        final double gelXAbs;
        final double gelYAbs;
        final double yInCrop;

        LoggedCropMarker(String label, double sourceXAbs, double sourceYAbs,
                double gelXAbs, double gelYAbs, double yInCrop) {
            this.label = label;
            this.sourceXAbs = sourceXAbs;
            this.sourceYAbs = sourceYAbs;
            this.gelXAbs = gelXAbs;
            this.gelYAbs = gelYAbs;
            this.yInCrop = yInCrop;
        }
    }

    private static final class ReconstructionImageRequest {
        final String originalPath;
        final int expectedWidth;
        final int expectedHeight;
        final List<String> roles = new ArrayList<String>();
        boolean required;
        boolean dimensionMismatch;
        boolean aspectRatioMismatch;
        boolean conflictingLoggedDimensions;
        LoadedImage loadedImage;

        ReconstructionImageRequest(String originalPath, int expectedWidth, int expectedHeight) {
            this.originalPath = originalPath;
            this.expectedWidth = expectedWidth;
            this.expectedHeight = expectedHeight;
        }

        void addRole(String role) {
            if (!roles.contains(role)) {
                roles.add(role);
            }
        }
    }

    private static final class ReconstructedGeometry {
        final double x;
        final double y;
        final int width;
        final int height;
        final double angleDeg;

        ReconstructedGeometry(double x, double y, int width, int height, double angleDeg) {
            this.x = x;
            this.y = y;
            this.width = width;
            this.height = height;
            this.angleDeg = angleDeg;
        }
    }

    private static final class AnnotatedMarkerImage {
        final ImagePlus imagePlus;
        final KdaMarkerSet markerSet;
        final double scaleX;
        final double scaleY;

        AnnotatedMarkerImage(ImagePlus imagePlus, KdaMarkerSet markerSet,
                double scaleX, double scaleY) {
            this.imagePlus = imagePlus;
            this.markerSet = markerSet;
            this.scaleX = scaleX;
            this.scaleY = scaleY;
        }
    }

    private enum MarkerSourceType {
        GEL_IMAGE("Gel image", "Gel"),
        MARKER_IMAGE("kDa marker image", "Marker");

        final String displayName;
        final String shortName;

        MarkerSourceType(String displayName, String shortName) {
            this.displayName = displayName;
            this.shortName = shortName;
        }
    }

    private static final class LoadedImage {
        final ImagePlus imagePlus;
        final String path;

        LoadedImage(ImagePlus imagePlus, String path) {
            this.imagePlus = imagePlus;
            this.path = path;
        }
    }

    private static final class KdaMarkerSet {
        final String id;
        final MarkerSourceType sourceType;
        final String sourcePath;
        final int sourceWidth;
        final int sourceHeight;
        final List<KdaMarker> markers = new ArrayList<KdaMarker>();
        boolean frozen;

        KdaMarkerSet(String id, MarkerSourceType sourceType, String sourcePath,
                int sourceWidth, int sourceHeight) {
            this.id = id;
            this.sourceType = sourceType;
            this.sourcePath = sourcePath;
            this.sourceWidth = sourceWidth;
            this.sourceHeight = sourceHeight;
        }

        boolean matchesSource(MarkerSourceType type, String path, int width, int height) {
            return sourceType == type && Controller.samePath(sourcePath, path)
                    && sourceWidth == width && sourceHeight == height;
        }

        KdaMarkerSet editableCopy(String newId) {
            KdaMarkerSet copy = new KdaMarkerSet(newId, sourceType, sourcePath,
                    sourceWidth, sourceHeight);
            copy.markers.addAll(markers);
            return copy;
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
        final double sourceXAbs;
        final double sourceYAbs;
        final double gelXAbs;
        final double gelYAbs;

        CropMarker(String label, double yInCrop,
                double sourceXAbs, double sourceYAbs,
                double gelXAbs, double gelYAbs) {
            this.label = label;
            this.yInCrop = yInCrop;
            this.sourceXAbs = sourceXAbs;
            this.sourceYAbs = sourceYAbs;
            this.gelXAbs = gelXAbs;
            this.gelYAbs = gelYAbs;
        }
    }

    private static final class MarkerMapping {
        final int markerWidth;
        final int markerHeight;
        final int gelWidth;
        final int gelHeight;
        final double scaleX;
        final double scaleY;
        final boolean dimensionsDiffer;
        final boolean aspectRatioMismatch;

        MarkerMapping(int markerWidth, int markerHeight, int gelWidth, int gelHeight,
                double scaleX, double scaleY,
                boolean dimensionsDiffer, boolean aspectRatioMismatch) {
            this.markerWidth = markerWidth;
            this.markerHeight = markerHeight;
            this.gelWidth = gelWidth;
            this.gelHeight = gelHeight;
            this.scaleX = scaleX;
            this.scaleY = scaleY;
            this.dimensionsDiffer = dimensionsDiffer;
            this.aspectRatioMismatch = aspectRatioMismatch;
        }
    }

    private static final class BandCrop {
        final BufferedImage image;
        final List<CropMarker> markers;
        final String label;
        final String sourcePath;
        final int sourceWidth;
        final int sourceHeight;
        final KdaMarkerSet markerSet;
        final MarkerMapping markerMapping;
        int displayWidth;
        double xOffset;
        double yOffset;
        double cropX;
        double cropY;
        int cropWidth;
        int cropHeight;
        double cropAngleDeg;

        BandCrop(BufferedImage image, List<CropMarker> markers, String label, int displayWidth,
                String sourcePath, int sourceWidth, int sourceHeight,
                KdaMarkerSet markerSet, MarkerMapping markerMapping) {
            this.image = image;
            this.markers = markers;
            this.label = label;
            this.displayWidth = displayWidth;
            this.sourcePath = sourcePath;
            this.sourceWidth = sourceWidth;
            this.sourceHeight = sourceHeight;
            this.markerSet = markerSet;
            this.markerMapping = markerMapping;
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
