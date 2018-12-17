package rup.ino.catornot;


import java.io.IOException;

public class MainActivitySkeleton {

    public void permissionGranted() {
        impl.safeCameraOpenDelayed(0);
    }

    public interface PreviewCallback {
        public void onPreviewFrame(byte[] data);
    }

    public interface CameraSkeleton {
        void stopPreview();

        void release();

        void startPreview();

        void setOneShotPreviewCallback(PreviewCallback action);

        void init() throws IOException;

        void setPreviewSize(int width, int height);
    }

    public interface Log {
        void i(String message);

        void e(String error);
    }

    public interface Impl {
        CameraSkeleton cameraOpen(int id);

        int invisible();

        SurfaceView findSurfaceView();

        TextView findTextView();

        int visible();

        void safeCameraOpenDelayed(int id);
    }

    public interface TextView {

        void setText(String txt);

        void setVisibility(int invisible);
    }

    public interface SurfaceView {

        int getWidth();

        int getHeight();
    }

    public TextView getTextView() {
        return mTextView;
    }

    public SurfaceView getSurfaceView() {
        return mSurfaceView;
    }

    private TextView mTextView;
    private SurfaceView mSurfaceView;
    private final Log log;
    private final Impl impl;
    private CameraSkeleton camera;
    private boolean isPreviewActive = false;

    public MainActivitySkeleton(Log log, Impl impl) {
        this.log = log;
        this.impl = impl;
    }

    public void stopPreview() {
        if (camera != null)
            camera.stopPreview();
        isPreviewActive = false;
        log.i("Stopped preview!");
    }

    /**
     * When this function returns, mCamera will be null.
     */
    private void stopPreviewAndFreeCamera() {

        if (camera != null) {
            // Call stopPreview() to stop updating the preview surface.
            stopPreview();

            // Important: Call release() to release the camera for use by other
            // applications. Applications should release the camera immediately
            // during onPause() and re-open() it during onResume()).
            camera.release();

            camera = null;
            log.i("Freed preview!");
        }
    }

    private void startPreview() {
        if (camera == null) throw new RuntimeException("You should not be here!");
        camera.setOneShotPreviewCallback(new PreviewCallback() {
            @Override
            public void onPreviewFrame(byte[] data) {
                isPreviewActive = true;
                log.i("Started preview!");
            }
        });
        camera.startPreview();

    }

    public boolean safeCameraOpen(int id) {
        try {
            stopPreviewAndFreeCamera();
            camera = impl.cameraOpen(id);
            if (camera == null) return false;
            camera.init();

            startPreview();
            log.i("Created camera!");
        } catch (Exception e) {
            log.e("failed to open Camera");
            e.printStackTrace();
            return false;
        }

        return true;
    }

    private void startPreviewMode() {
        if (camera == null)
            safeCameraOpen(0);
        else
            startPreview();
        log.i("Going to preview mode!");
        mTextView.setVisibility(impl.invisible());
    }

    private void startPhotoMode() {
        if (camera == null)
            throw new RuntimeException("You shouldn't get here!");
        log.i("Going to photo mode!");
        stopPreview();
        if (Math.random() > 0.5) {
            log.i("No cat!");
            mTextView.setText("Nie ma kota");
        } else {
            log.i("Is cat!");
            mTextView.setText("Jest kot");
        }
        mTextView.setVisibility(impl.visible());
    }

    public void takePhoto() {
        log.i("Taking photo!");
        if (!isPreviewActive) {
            startPreviewMode();
        } else {
            startPhotoMode();
        }
    }

    public void onCreate() {

        mSurfaceView = impl.findSurfaceView();
        mTextView = impl.findTextView();

    }


    public void surfaceChanged() {
        if (camera != null) {
            log.i("Changed surface!");
            camera.setPreviewSize(mSurfaceView.getWidth(), mSurfaceView.getHeight());
            startPreview();
        }

    }

    public void surfaceDestroyed() {
        if (camera != null) {
            stopPreview();
        }
    }

    public void onDestroy() {
        stopPreviewAndFreeCamera();
    }
}
