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

        //@ensures \result != null;
        //@ensures \result.takePhotoText == true;
        //@ensures \result.enabled == true;
        //@assignable \nothing;
        MainActivitySkeleton.MenuItem findTakePhotoButton();

        //@assignable \nothing;
        //@ensures \result != null;
        ProgressBar findProgressBar();

        /*@ pure @*/ int visible();

        //@assignable \nothing;
        //@ensures \result != null;
        Handler getHandler();

        //@assignable callbacksAttached;
        //@ensures callbacksAttached == true;
        void attachCallbacks();

        //@assignable \nothing;
        void showDialog(String s);

        //@assignable \nothing;
        void sleep(long milis);

        //@assignable \nothing;
        void startThread(Runnable runnable);

        //@assignable \nothing;
        //@ensures \result != null;
        PermissionHandler getPermissionHandler();

    }

    public interface TextView {

        //@assignable \nothing;
        void setTextNoCat();

        //@assignable \nothing;
        void setTextIsCat();

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

    public interface MenuItem {

        //@public instance ghost boolean enabled = true;
        //@public instance ghost boolean takePhotoText = false;

        //@ensures takePhotoText == true;
        //@assignable takePhotoText;
        void setTakePhotoText();

        //@ensures takePhotoText == false;
        //@assignable takePhotoText;
        void setTakeNextPhotoText();

        //@ensures enabled == t;
        //@assignable enabled;
        void setEnabled(boolean t);
    }

    public static class Handler {

        //@requires s.camera == null;
        //@requires s.mTextView != null;
        //@requires s.mHolder != null;
        //@requires s.mProgressBar != null;
        //@requires s.camera != null ==> s.camera.released == true;
        //@requires s.mMenuItem.enabled == true;
        //@ensures s.camera.previewed == s.isPreviewActive;
        //@ensures s.camera.released == false;
        //@ensures s.camera != null;
        //@requires s.mMenuItem != null;
        //@ensures s.mMenuItem.takePhotoText == s.isPreviewActive;
        //@ensures s.mMenuItem.enabled == true;
        //@assignable s.camera;
        //@assignable s.camera.previewed;
        //@assignable s.mMenuItem.takePhotoText;
        //@assignable s.mMenuItem.enabled;
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
        //@requires s.mMenuItem != null;
        //@requires s.mMenuItem.enabled == false;
        //@ensures s.mMenuItem.enabled == true;
        //@ensures s.mMenuItem.takePhotoText == false;
        //@assignable s.mMenuItem.takePhotoText;
        //@assignable s.mMenuItem.enabled;
        public void postProgressFinalizer(/*@ non_null @*/ MainActivitySkeleton  s) {
            s.mProgressBar.setVisibility(s.impl.invisible());
            if (s.isCat) {
                s.log.i("Is cat!");
                s.mTextView.setTextIsCat();
            } else {
                s.log.i("No cat!");
                s.mTextView.setTextNoCat();
            }
            s.mTextView.setVisibility(s.impl.visible());
            s.mMenuItem.setTakeNextPhotoText();
            s.mMenuItem.setEnabled(true);
        }

        //@requires s.mProgressBar != null;
        //@requires progress >= 0;
        //@assignable \nothing;
        public void postProgressUpdater(/*@ non_null @*/ MainActivitySkeleton s, int progress) {
            s.mProgressBar.setProgress(progress);
        }

        //@requires s.mProgressBar != null;
        //@requires s.mTextView != null;
        //@requires s.mMenuItem != null;
        //@requires s.mMenuItem.enabled == false;
        //@ensures s.mMenuItem.takePhotoText == false;
        //@ensures s.mMenuItem.enabled == true;
        //@assignable s.mMenuItem.takePhotoText;
        //@assignable s.mMenuItem.enabled;
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


    public static class PermissionHandler{

        //@requires skel.camera != null ==> skel.camera.released == false;
        //@ensures skel.mSurfaceView != null;
        //@ensures skel.mProgressBar != null;
        //@ensures skel.mTextView != null;
        //@ensures skel.mHolder != null;
        //@ensures skel.isPreviewActive == true;
        //@ensures skel.mMenuItem != null;
        //@assignable skel.isPreviewActive;
        //@assignable skel.mTextView;
        //@assignable skel.mProgressBar;
        //@assignable skel.mSurfaceView;
        //@assignable skel.mHolder;
        //@assignable skel.camera;
        //@assignable skel.mMenuItem;
        //@assignable skel.camera.previewed;
        //@assignable skel.mHolder.callbacksAttached;
        //@assignable skel.impl.callbacksAttached;
        //@assignable skel.mMenuItem.takePhotoText;
        //@assignable skel.mMenuItem.enabled;
        //@ensures skel.mHolder.callbacksAttached == true;
        //@ensures skel.impl.callbacksAttached == true;
        //@ensures skel.camera != null;
        //@ensures skel.mMenuItem.takePhotoText == true;
        //@ensures skel.mMenuItem.enabled == true;
        //@ensures skel.camera.previewed == skel.isPreviewActive;
        //@ensures skel.camera.released == false;
        void checkPermissions(MainActivitySkeleton skel){
            skel.permissionGranted();
        }

    }

    private /*@ spec_public nullable @*/ TextView mTextView;
    private /*@ spec_public nullable @*/ MenuItem mMenuItem;
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

    //@requires camera != null ==> camera.released == false;
    //@ensures mSurfaceView != null;
    //@ensures mProgressBar != null;
    //@ensures mTextView != null;
    //@ensures mHolder != null;
    //@ensures isPreviewActive == true;
    //@ensures mMenuItem != null;
    //@assignable isPreviewActive;
    //@assignable mTextView;
    //@assignable mProgressBar;
    //@assignable mSurfaceView;
    //@assignable mHolder;
    //@assignable camera;
    //@assignable mMenuItem;
    //@assignable camera.previewed;
    //@assignable mHolder.callbacksAttached;
    //@assignable impl.callbacksAttached;
    //@assignable mMenuItem.takePhotoText;
    //@assignable mMenuItem.enabled;
    //@ensures mHolder.callbacksAttached == true;
    //@ensures impl.callbacksAttached == true;
    //@ensures camera != null;
    //@ensures mMenuItem.takePhotoText == true;
    //@ensures mMenuItem.enabled == true;
    //@ensures camera.previewed == isPreviewActive;
    //@ensures camera.released == false;
    private void ensureEverythingWorks() {
        log.i("ensureEverythingWorks!");
        PermissionHandler ph = impl.getPermissionHandler();
        ph.checkPermissions(this);
    }

    //@requires camera != null ==> camera.released == false;
    //@ensures mSurfaceView != null;
    //@ensures mProgressBar != null;
    //@ensures mTextView != null;
    //@ensures mHolder != null;
    //@ensures isPreviewActive == true;
    //@ensures mMenuItem != null;
    //@assignable isPreviewActive;
    //@assignable mTextView;
    //@assignable mProgressBar;
    //@assignable mSurfaceView;
    //@assignable mHolder;
    //@assignable camera;
    //@assignable mMenuItem;
    //@assignable camera.previewed;
    //@assignable mHolder.callbacksAttached;
    //@assignable impl.callbacksAttached;
    //@assignable mMenuItem.takePhotoText;
    //@assignable mMenuItem.enabled;
    //@ensures mMenuItem.enabled == true;
    //@ensures mHolder.callbacksAttached == true;
    //@ensures impl.callbacksAttached == true;
    //@ensures camera != null;
    //@ensures mMenuItem.takePhotoText == true;
    //@ensures camera.previewed == isPreviewActive;
    //@ensures camera.released == false;
    public void permissionGranted() {
        log.i("permissionGranted");
        if (mSurfaceView == null)
            mSurfaceView = impl.findSurfaceView();
        if (mTextView == null)
            mTextView = impl.findTextView();
        if (mProgressBar == null)
            mProgressBar = impl.findProgressBar();
        if (mMenuItem == null)
            mMenuItem = impl.findTakePhotoButton();
        else
            mMenuItem.setEnabled(true);
        impl.attachCallbacks();
        if (mHolder == null)
            mHolder = mSurfaceView.getHolder();
        mHolder.addCallback();
        isPreviewActive = true;
        if (camera == null) {
            //@assert mMenuItem.enabled == true;
            impl.getHandler().postDelayedCameraOpener(this, 100);
            //@assert mMenuItem.enabled == true;
        } else {
            //@assert camera != null;
            //@assert camera.released == false;
            //@assert mMenuItem.enabled == true;
            updateMode();
            //@assert mMenuItem.enabled == true;
            //@assert camera != null;
        }

    }

    //@ensures camera == null;
    //@ensures mHolder == null;
    //@ensures isPreviewActive == true;
    //@requires camera != null ==> camera.released == false;
    private void ensureEverythingDestroyed() {
        log.i("ensureEverythingDestroyed!");
        if (camera != null) {
            camera.stopPreview();
            camera.release();
            //@assert camera.released == true;
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
    //@requires mMenuItem != null;
    //@requires isPreviewActive ==> mMenuItem.enabled;
    //@requires camera.released == false;
    //@ensures camera.previewed == isPreviewActive;
    //@ensures mMenuItem.takePhotoText == isPreviewActive;
    //@ensures mMenuItem.enabled == true;
    //@assignable camera.previewed;
    //@assignable mMenuItem.takePhotoText;
    //@assignable mMenuItem.enabled;
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
            mMenuItem.setTakePhotoText();
        } else {
            log.i("startPhotoMode");
            camera.stopPreview();
            mProgressBar.setProgress(0);
            mProgressBar.setVisibility(impl.visible());
            final Handler handler = impl.getHandler();
            mMenuItem.setEnabled(false);
            //@assert mMenuItem.enabled == false;
            handler.startProgressBarThread(this);
            //@assert mMenuItem.enabled == true;

        }
    }

    //@requires camera != null;
    //@requires camera.released == false;
    //@requires mSurfaceView != null;
    //@requires mTextView != null;
    //@requires mProgressBar != null;
    //@requires mMenuItem != null;
    //@requires mMenuItem.enabled == true;
    //@assignable isCat;
    //@assignable isPreviewActive;
    //@assignable camera.previewed;
    //@assignable mMenuItem.takePhotoText;
    //@assignable mMenuItem.enabled;
    //@ensures isPreviewActive == !\old(isPreviewActive);
    //@ensures camera.previewed == isPreviewActive;
    //@ensures mMenuItem.takePhotoText == isPreviewActive;
    //@ensures mMenuItem.enabled == true;
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
    //@requires camera != null ==> mMenuItem != null;
    //@requires camera != null ==> camera.released == false;
    //@requires camera != null ==> mMenuItem.enabled == true;
    //@assignable camera.previewed;
    //@assignable mMenuItem.takePhotoText;
    //@assignable mMenuItem.enabled;
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
    //@ensures camera == null;
    //@ensures mHolder == null;
    //@ensures isPreviewActive == true;
    public void onDestroy() {
        log.i("onDestroy");
        ensureEverythingDestroyed();
    }

    //@ensures mSurfaceView != null;
    //@ensures mProgressBar != null;
    //@ensures mTextView != null;
    //@ensures mHolder != null;
    //@ensures isPreviewActive == true;
    //@ensures mMenuItem != null;
    //@assignable isPreviewActive;
    //@assignable mTextView;
    //@assignable mProgressBar;
    //@assignable mSurfaceView;
    //@assignable mHolder;
    //@assignable camera;
    //@assignable mMenuItem;
    //@assignable camera.previewed;
    //@assignable mHolder.callbacksAttached;
    //@assignable impl.callbacksAttached;
    //@assignable mMenuItem.takePhotoText;
    //@assignable mMenuItem.enabled;
    //@ensures mHolder.callbacksAttached == true;
    //@ensures impl.callbacksAttached == true;
    //@ensures camera != null;
    //@ensures mMenuItem.takePhotoText == true;
    //@ensures mMenuItem.enabled == true;
    //@ensures camera.previewed == isPreviewActive;
    //@ensures camera.released == false;
    //@requires camera != null ==> camera.released == false;
    public void onCreate() {
        log.i("onCreate");
        ensureEverythingWorks();
        impl.showDialog("Aby zapewnić poprawne działanie apliakcji, " +
                "należy wykonywać wyłącznie zdjęcia telewizora." +
                " W przeciwnym wypadku wynik" +
                " może być niezgodny z prawdą.");
    }

    //@requires camera != null ==> camera.released == false;
    //@ensures camera == null;
    //@ensures mHolder == null;
    //@ensures isPreviewActive == true;
    public void onStop() {
        log.i("onStop");
        ensureEverythingDestroyed();
    }

    public void surfaceCreated() {
        log.i("surfaceCreated");
    }

    //@requires camera != null ==> camera.released == false;
    //@ensures camera == null;
    //@ensures mHolder == null;
    //@ensures isPreviewActive == true;
    public void onPause() {
        log.i("onPause");
        ensureEverythingDestroyed();
    }

    //@ensures mSurfaceView != null;
    //@ensures mProgressBar != null;
    //@ensures mTextView != null;
    //@ensures mHolder != null;
    //@ensures isPreviewActive == true;
    //@ensures mMenuItem != null;
    //@assignable isPreviewActive;
    //@assignable mTextView;
    //@assignable mProgressBar;
    //@assignable mSurfaceView;
    //@assignable mHolder;
    //@assignable camera;
    //@assignable mMenuItem;
    //@assignable camera.previewed;
    //@assignable mHolder.callbacksAttached;
    //@assignable impl.callbacksAttached;
    //@assignable mMenuItem.takePhotoText;
    //@assignable mMenuItem.enabled;
    //@ensures mHolder.callbacksAttached == true;
    //@ensures impl.callbacksAttached == true;
    //@ensures camera != null;
    //@ensures mMenuItem.takePhotoText == true;
    //@ensures mMenuItem.enabled == true;
    //@ensures camera.previewed == isPreviewActive;
    //@ensures camera.released == false;
    //@requires camera != null ==> camera.released == false;
    public void onResume() {
        log.i("onResume");
        ensureEverythingWorks();
    }

    //@requires camera == null;
    //@requires mSurfaceView == null;
    //@requires mTextView == null;
    //@requires mProgressBar == null;
    //@requires mMenuItem == null;
    //@ensures camera == null;
    //@ensures mSurfaceView == null;
    //@ensures mTextView == null;
    //@ensures mProgressBar == null;
    //@ensures mMenuItem == null;
    //@requires pauseCounts.length > 0;
    //@requires pauseCounts.length == photoTakes.length;
    //@requires \forall int i; 0 <= i && i < pauseCounts.length; pauseCounts[i] >= 0 && photoTakes[i] >= 0;
    public void simulateAppLifecycle(int[] pauseCounts,int[] photoTakes){
        //@maintaining 0 <= i && i <= pauseCounts.length;
        for(int i =0;i<pauseCounts.length;i++) {
            onCreate();
            //@assert camera != null;
            //@assert isPreviewActive == true;
            //@assert camera.released == false;
            //@assert camera.previewed == true;
            //@assert mSurfaceView != null;
            //@assert mTextView != null;
            //@assert mProgressBar != null;
            //@assert mMenuItem != null;
            //@assert mMenuItem.takePhotoText == true;

            //@maintaining 0 <= j && j <= pauseCounts[i];
            for (int j = 0;j<pauseCounts[i];j++) {
                onResume();
                //@assert camera != null;
                //@assert isPreviewActive == true;
                //@assert camera.released == false;
                //@assert camera.previewed == true;
                //@assert mSurfaceView != null;
                //@assert mTextView != null;
                //@assert mProgressBar != null;
                //@assert mMenuItem != null;
                //@assert mMenuItem.takePhotoText == true;

                //@ghost boolean previewActive = true;
                //@maintaining 0 <= k && k <= photoTakes[i] && previewActive == isPreviewActive;
                for (int k=0;k<photoTakes[i];k++) {
                    takePhoto();
                    //@set previewActive = !previewActive;
                    //@assert isPreviewActive == previewActive;
                    //@assert camera.previewed == previewActive;
                    //@assert mMenuItem.takePhotoText == previewActive;

                    //@assert camera != null;
                    //@assert camera.released == false;
                    //@assert mSurfaceView != null;
                    //@assert mTextView != null;
                    //@assert mProgressBar != null;
                    //@assert mMenuItem != null;

                }

                onPause();
                //@assert camera == null;
            }
            onDestroy();
            //@assert camera == null;
        }
    }
}
