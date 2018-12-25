package rup.ino.catornot;


import java.io.IOException;

public class MainActivitySkeleton {

    public interface Runnable {

        void run();
    }

    public interface PreviewCallback {

        public void onPreviewFrame(byte[] data);
    }

    public interface CameraSkeleton {
        //@public instance ghost boolean released;
        //@public instance ghost boolean previewed;

        //@assignable previewed;
        //@requires released == false;
        //@ensures previewed == false;
        void stopPreview();

        //@assignable released;
        //@requires released == false;
        //@ensures released == true;
        void release();

        //@assignable previewed;
        //@requires released == false;
        //@ensures previewed == true;
        void startPreview();

        void reconnect() throws IOException;


        //@assignable \nothing;
        void setOneShotPreviewCallback(PreviewCallback action);

        //@assignable \nothing;
        void setDisplayOrientation() throws IOException;

        //@assignable \nothing;
        void setPreviewDisplay(SurfaceHolder holder) throws IOException;

        //@assignable \nothing;
        void setPreviewSize(int width, int height);
    }

    public interface Log {
        //@assignable \nothing;
        void i(String message);

        //@assignable \nothing;
        void e(String error);
    }

    public interface Impl {

        //@public instance ghost boolean callbacksAttached = false;

        //@ensures \result != null;
        //@ensures \result.released == false;
        //@ensures \result.previewed == false;
        //@assignable \nothing;
        CameraSkeleton cameraOpen(int id);


        /*@ pure @*/ int invisible();


        //@ensures \result != null;
        //@assignable \nothing;
        SurfaceView findSurfaceView();

        //@ensures \result != null;
        //@assignable \nothing;
        TextView findTextView();

        //@assignable \nothing;
        //@ensures \result != null;
        ProgressBar findProgressBar();

        /*@ pure @*/ int visible();

        //@assignable \nothing;
        //@ensures \result != null;
        Handler getHandler();

        //@assignable \nothing;
        void checkPermissions();

        //@assignable callbacksAttached;
        //@ensures callbacksAttached == true;
        void attachCallbacks();

        //@assignable \nothing;
        void showDialog(String s);

        //@assignable \nothing;
        void sleep(long milis);

        //@assignable \nothing;
        void startThread(Runnable runnable);
    }

    public interface TextView {

        //@assignable \nothing;
        void setText(String txt);

        //@assignable \nothing;
        void setVisibility(int invisible);
    }

    public interface SurfaceView {

        //@assignable \nothing;
        int getWidth();

        //@assignable \nothing;
        int getHeight();

        //@assignable \nothing;
        //@ensures \result != null;
        //@ensures \result.callbacksAttached == false;
        SurfaceHolder getHolder();
    }

    public interface SurfaceHolder {

        //@public instance ghost boolean callbacksAttached = false;

        //@assignable callbacksAttached;
        //@ensures callbacksAttached == true;
        void addCallback();

        //@assignable callbacksAttached;
        //@ensures callbacksAttached == false;
        void removeCallback();
    }

    public interface ProgressBar {

        //@assignable \nothing;
        void setVisibility(int v);

        //@assignable \nothing;
        void setProgress(int progress);

        //@assignable \nothing;
        //@ensures \result <= 9999;
        //@ensures \result > 0;
        int getMax();

    }

    public static class Handler {

        //@requires s.camera == null;
        //@requires s.mTextView != null;
        //@requires s.mHolder != null;
        //@requires s.mProgressBar != null;
        //@requires s.camera != null ==> s.camera.released == true;
        //@ensures s.camera.previewed == s.isPreviewActive;
        //@ensures s.camera != null;
        //@assignable s.camera;
        //@assignable s.camera.previewed;
        public void postDelayedCameraOpener(/*@ non_null @*/ MainActivitySkeleton  s, long delayMilis) {
            //@assert s.mHolder != null;
            s.camera = s.impl.cameraOpen(0);
            //@assert s.camera != null;
            //@assert s.camera != null;
            //@assert s.mHolder != null;
            s.log.i("created camera!");
            //@assert s.camera != null;
            //@assert s.mHolder != null;
            try {
                s.camera.setDisplayOrientation();
                //@assert s.camera != null;
                //@assert s.mHolder != null;
                s.camera.setPreviewDisplay(s.mHolder);
            } catch (Exception e) {

            }
            s.updateMode();
        }

        //@requires s.mTextView != null;
        //@requires s.mProgressBar != null;
        //@assignable \nothing;
        public void postProgressFinalizer(/*@ non_null @*/ MainActivitySkeleton  s) {
            s.mProgressBar.setVisibility(s.impl.invisible());
            if (s.isCat) {
                s.log.i("Is cat!");
                s.mTextView.setText("Jest kot");
            } else {
                s.log.i("No cat!");
                s.mTextView.setText("Nie ma kota");
            }
            s.mTextView.setVisibility(s.impl.visible());
        }

        //@requires s.mProgressBar != null;
        //@requires progress >= 0;
        //@assignable \nothing;
        public void postProgressUpdater(/*@ non_null @*/ MainActivitySkeleton s, int progress) {
            s.mProgressBar.setProgress(progress);
        }

        //@requires s.mProgressBar != null;
        //@requires s.mTextView != null;
        //@assignable \nothing;
        public void startProgressBarThread(/*@ non_null @*/ MainActivitySkeleton s) {
            //@maintaining 0 < i && i <= 101;
            for (int i = 1; i <= 100; i++) {
                //@assert i > 0;
                //@assert i <= 100;
                final double rand = Math.random();
                //@assert rand >= 0;
                //@assert rand < 1;
                final double sleepTime = rand * 100;
                //@assert sleepTime >= 0;
                //@assert sleepTime < 100;
                s.impl.sleep((long) sleepTime);
                s.log.i("" + i);
                final int max = s.mProgressBar.getMax();
                final int progress = (int) (max * i / 100);
                //@assert i <= 100;
                //@assert i > 0;
                //@assert max > 0;
                //@assert max <= 9999;
                //@assert 0 <= max * i ;
                //@assert max * i <= 999900;
                //@assert max * i / 100 <= 9999;
                //@assert max * 100 >= max * i;
                //@assert progress >= 0;
                postProgressUpdater(s, progress);

            }
            postProgressFinalizer(s);
        }
    }


    private /*@ spec_public nullable @*/ TextView mTextView;
    private /*@ spec_public nullable @*/ SurfaceView mSurfaceView;
    private /*@ spec_public nullable @*/ ProgressBar mProgressBar;
    private /*@ spec_public nullable @*/ SurfaceHolder mHolder;
    private /*@ non_null@*/ final Log log;
    private /*@ non_null spec_public @*/ final Impl impl;
    private /*@ spec_public nullable @*/ CameraSkeleton camera;
    private /*@ spec_public @*/ boolean isPreviewActive = true;
    private /*@ spec_public @*/ boolean isCat = false;

    //@assignable isCat;
    private void nextRandomCat() {
        log.i("nextRandomCat!");
        isCat = Math.random() > 0.5;
    }


    //@requires impl.callbacksAttached == false;
    public MainActivitySkeleton(/*@ non_null @*/ Log log, /*@ non_null @*/ Impl impl) {
        this.log = log;
        this.impl = impl;
    }

    private void ensureEverythingWorks() {
        log.i("ensureEverythingWorks!");
        impl.checkPermissions();
    }

    //@requires camera != null ==> camera.released == false;
    //@ensures mSurfaceView != null;
    //@ensures mProgressBar != null;
    //@ensures mTextView != null;
    //@ensures mHolder != null;
    //@ensures isPreviewActive == true;
    //@assignable isPreviewActive;
    //@assignable mTextView;
    //@assignable mProgressBar;
    //@assignable mSurfaceView;
    //@assignable mHolder;
    //@assignable camera;
    //@assignable camera.previewed;
    //@assignable mHolder.callbacksAttached;
    //@assignable impl.callbacksAttached;
    //@ensures mHolder.callbacksAttached == true;
    //@ensures impl.callbacksAttached == true;
    //@ensures camera != null;
    public void permissionGranted() {
        log.i("permissionGranted");
        if (mSurfaceView == null)
            mSurfaceView = impl.findSurfaceView();
        if (mTextView == null)
            mTextView = impl.findTextView();
        if (mProgressBar == null)
            mProgressBar = impl.findProgressBar();
        impl.attachCallbacks();
        if (mHolder == null)
            mHolder = mSurfaceView.getHolder();
        mHolder.addCallback();

        isPreviewActive = true;
        if (camera == null) {
            impl.getHandler().postDelayedCameraOpener(this, 100);
        } else {
            //@assert camera != null;
            //@assert camera.released == false;
            updateMode();
            //@assert camera != null;
        }

    }

    //@ensures camera == null;
    //@requires camera != null ==> camera.released == false;
    private void ensureEverythingDestroyed() {
        log.i("ensureEverythingDestroyed!");
        if (camera != null) {
            camera.stopPreview();
            camera.release();
            camera = null;
            log.i("camera = null!");
        }
        if (mHolder != null) {
            mHolder.removeCallback();
            mHolder = null;
            log.i("mHolder = null!");
        }
        isPreviewActive = true;
    }

    //@requires camera != null;
    //@requires mProgressBar != null;
    //@requires mTextView != null;
    //@requires camera.released == false;
    //@ensures camera.previewed == isPreviewActive;
    //@assignable camera.previewed;
    private void updateMode() {
        log.i("updateMode!");
        if (isPreviewActive) {
            log.i("startPreviewMode");
            camera.setOneShotPreviewCallback(new PreviewCallback() {
                @Override
                public void onPreviewFrame(byte[] data) {
                    isPreviewActive = true;
                    log.i("Started preview!");
                }
            });
            camera.startPreview();
            mTextView.setVisibility(impl.invisible());
        } else {
            log.i("startPhotoMode");
            camera.stopPreview();
            mProgressBar.setProgress(0);
            mProgressBar.setVisibility(impl.visible());
            final Handler handler = impl.getHandler();
            handler.startProgressBarThread(this);

        }

    }


    //@requires camera != null;
    //@requires camera.released == false;
    //@requires mSurfaceView != null;
    //@requires mTextView != null;
    //@requires mProgressBar != null;
    //@assignable isCat;
    //@assignable isPreviewActive;
    //@assignable camera.previewed;
    //@ensures isPreviewActive != \old(isPreviewActive);
    public void takePhoto() {
        log.i("takePhoto");
        isPreviewActive = !isPreviewActive;
        if (!isPreviewActive) {
            nextRandomCat();
        }
        updateMode();
    }


    //@requires camera != null ==> mProgressBar != null;
    //@requires camera != null ==> mSurfaceView != null;
    //@requires camera != null ==> mTextView != null;
    //@requires camera != null ==> camera.released == false;
    //@assignable camera.previewed;
    public void surfaceChanged() {
        log.i("surfaceChanged");
        if (camera != null) {
            log.i("Changed surface!");
            camera.setPreviewSize(mSurfaceView.getWidth(), mSurfaceView.getHeight());
            updateMode();
        }

    }

    //@assignable camera.previewed;
    //@requires camera != null ==> camera.released == false;
    //@ensures camera != null ==> camera.previewed == false;
    public void surfaceDestroyed() {
        log.i("surfaceDestroyed");
        if (camera != null) {
            camera.stopPreview();
        }
    }

    //@requires camera != null ==> camera.released == false;
    public void onDestroy() {
        log.i("onDestroy");
        ensureEverythingDestroyed();
    }


    public void onCreate() {
        log.i("onCreate");
        ensureEverythingWorks();
        impl.showDialog("Algorytmy mogą nie działać poprawnie " +
                "jeżeli na zdjęciu nie ma żadnego zwierzęcia");
    }

    //@requires camera != null ==> camera.released == false;
    public void onStop() {
        log.i("onStop");
        ensureEverythingDestroyed();
    }

    public void surfaceCreated() {
        log.i("surfaceCreated");
    }

    //@requires camera != null ==> camera.released == false;
    public void onPause() {
        log.i("onPause");
        ensureEverythingDestroyed();
    }

    public void onResume() {
        log.i("onResume");
        ensureEverythingWorks();
    }


}
