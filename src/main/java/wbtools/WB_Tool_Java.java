package wbtools;

import ij.plugin.PlugIn;
import javax.swing.SwingUtilities;

public class WB_Tool_Java implements PlugIn {
    @Override
    public void run(String arg) {
        SwingUtilities.invokeLater(new Runnable() {
            @Override
            public void run() {
                new WBToolJava.Controller().showFrame();
            }
        });
    }
}
