# wbtool-fiji-plugin
Fiji plugin for making blot figures

Download the ".py" file, put it in Fiji's "plugins" folder and enjoy

## Java rewrite (in progress)

The Java plugin can use a separate image as the kDa-marker source:

1. Click **Open kDa Marker Image...** and choose the ladder/marker image.
2. Click **Mark kDa Bands**, click each band in the marker image, and enter its label.
3. Click **Open Gel Image...** and choose the image that will be cropped.
4. Crop the gel image. The markers are transferred into gel coordinates and included
   in every crop whose vertical range contains them.

If the marker image and gel image have different pixel dimensions, marker coordinates
are scaled proportionally to the gel width and height. If no separate marker image is
opened, marking continues to work directly on the gel image as before.

The gel uses Fiji's Rotated Rectangle tool whether or not crop mode has already been
started. You can draw and rotate the selection first and then click **Crop Region ->
Figure**, or click the crop button first, draw and rotate, and then click **Confirm
Crop**. A completed selection is cleared after it is added, so it cannot be reused by
accident.

The selected crop is outlined in cyan in the editor. This is only a selection indicator;
PDF export ignores it and draws the usual black frame around every crop.



# Citation

If you use WBtool to prepare figures for a publication, please cite the version of the tool that you used.

Maria A. Pirozhkova, Elisheva Babitz. WBtool-Fiji: an ImageJ/Fiji plugin for western blot figure assembly and annotation. GitHub repository: https://github.com/masha-rgfj/wbtool-fiji-plugin 2026


## Contributions

- Maria A. Pirozhkova — concept, software development, implementation, maintenance
- Elisheva Babitz — documentation, user manuals, installation support, testing, user onboarding, and dissemination
