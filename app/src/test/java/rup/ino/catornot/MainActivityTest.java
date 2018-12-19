package rup.ino.catornot;


import java.io.IOException;

public class MainActivityTest {
    static class Log implements MainActivitySkeleton.Log {

        @Override
        public void i(String message) {

        }

        @Override
        public void e(String error) {

        }
    }

    static class Camera implements MainActivitySkeleton.CameraSkeleton {

        boolean previewWorking = false;
        boolean released = false;
        boolean initialized = false;

        @Override
        public void stopPreview() {
            previewWorking = false;
        }

        @Override
        public void release() {
            released = true;
        }

        @Override
        public void startPreview() {
            previewWorking = true;
        }

        @Override
        public void setOneShotPreviewCallback(MainActivitySkeleton.PreviewCallback action) {
            action.onPreviewFrame(null);
        }

        @Override
        public void init() throws IOException {
            initialized = true;
        }

        @Override
        public void setPreviewSize(int width, int height) {

        }
    }

    static class SurfaceView implements MainActivitySkeleton.SurfaceView {

        @Override
        public int getWidth() {
            return 0;
        }

        @Override
        public int getHeight() {
            return 0;
        }
    }

    static class TextView implements MainActivitySkeleton.TextView {

        boolean visible = false;
        @Override
        public void setText(String txt) {

        }

        @Override
        public void setVisibility(int v) {
            visible = v == 1;
        }
    }

    static class Impl implements MainActivitySkeleton.Impl {

        @Override
        public MainActivitySkeleton.CameraSkeleton cameraOpen(int id) {
            return new Camera();
        }

        @Override
        public int invisible() {
            return 0;
        }

        @Override
        public MainActivitySkeleton.SurfaceView findSurfaceView() {
            return new SurfaceView();
        }

        @Override
        public MainActivitySkeleton.TextView findTextView() {
            return new TextView();
        }

        @Override
        public int visible() {
            return 1;
        }

        @Override
        public void safeCameraOpenDelayed(int id) {

        }
    }

    MainActivitySkeleton skeleton = new MainActivitySkeleton(new Log(), new Impl());


    void staticTest(){

    }
}