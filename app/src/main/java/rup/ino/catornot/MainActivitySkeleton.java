package rup.ino.catornot;


import java.io.IOException;

public class MainActivitySkeleton {

    public interface PreviewCallback {
        public void onPreviewFrame(byte[] data);
    }

    public interface CameraSkeleton {
        void stopPreview();

        void release();

        void startPreview();

        void reconnect() throws IOException;

        void setOneShotPreviewCallback(PreviewCallback action);

        void setDisplayOrientation() throws IOException;

        void setPreviewDisplay(SurfaceHolder holder) throws IOException;

        void setPreviewSize(int width, int height);
    }

    public interface Log {
        void i(String message);

        void e(String error);
    }

    public interface Impl {
        CameraSkeleton cameraOpen(int id);

        int invisible();

        /*@
         ensures \result != null;
         @*/
        SurfaceView findSurfaceView();

        /*@
         ensures \result != null;
         @*/
        TextView findTextView();

        int visible();

        void postDelayed(Runnable runnable, long delayMilis);

        void checkPermissions();

        void attachCallbacks();
    }

    public interface TextView {

        void setText(String txt);

        void setVisibility(int invisible);
    }

    public interface SurfaceView {

        int getWidth();

        int getHeight();

        SurfaceHolder getHolder();
    }

    public TextView getTextView() {
        return mTextView;
    }

    public SurfaceView getSurfaceView() {
        return mSurfaceView;
    }

    public interface SurfaceHolder{

        void addCallback();

        void removeCallback();
    }

    private /*@ spec_public @*/ TextView mTextView;
    private /*@ spec_public @*/ SurfaceView mSurfaceView;
    private SurfaceHolder mHolder;
    private /*@ non_null@*/ final Log log;
    private /*@ non_null spec_public @*/ final Impl impl;
    private /*@ spec_public @*/ CameraSkeleton camera;
    private /*@ spec_public @*/ boolean isPreviewActive = true;
    private /*@ spec_public @*/ boolean isCat = false;

    private void nextRandomCat(){
        log.i("nextRandomCat!");
        isCat = Math.random() > 0.5;
    }


    public MainActivitySkeleton(/*@ non_null @*/ Log log, /*@ non_null @*/ Impl impl) {
        this.log = log;
        this.impl = impl;
    }

    /*@
     ensures camera != null;
     @*/
    private void ensureEverythingWorks() {
        log.i("ensureEverythingWorks!");
        impl.checkPermissions();
    }

    public void permissionGranted() {
        log.i("permissionGranted");
        if (mSurfaceView == null)
            mSurfaceView = impl.findSurfaceView();
        if (mTextView == null)
            mTextView = impl.findTextView();
        impl.attachCallbacks();
        if (mHolder == null)
            mHolder = mSurfaceView.getHolder();
        mHolder.addCallback();

        isPreviewActive = true;
        if(camera==null) {
            impl.postDelayed(new Runnable() {
                @Override
                public void run() {
                    try {
                        //@assert camera == null;
                        camera = impl.cameraOpen(0);
                        log.i("created camera!");
                        camera.setDisplayOrientation();
                        camera.setPreviewDisplay(mHolder);

                        updateMode();
                    } catch (Exception e) {
                        log.e("failed to open Camera");
                        e.printStackTrace();
                    }
                }
            },100);
        }else{
            updateMode();
        }

    }

    /*@
     ensures camera != null;
     @*/
    private void ensureEverythingDestroyed() {
        log.i("ensureEverythingDestroyed!");
        if(camera!=null){
            camera.stopPreview();
            camera.release();
            camera = null;
            log.i("camera = null!");
        }
        if(mHolder!=null){
            mHolder.removeCallback();
            mHolder = null;
            log.i("mHolder = null!");
        }
        isPreviewActive = true;
    }

    /*@
     requires camera != null;
     requires mTextView != null;
     @*/
    private void updateMode() {
        log.i("updateMode!");
        if(isPreviewActive){
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
        }else{
            log.i("startPhotoMode");
            camera.stopPreview();
            if (isCat) {
                log.i("Is cat!");
                mTextView.setText("Jest kot");
            } else {
                log.i("No cat!");
                mTextView.setText("Nie ma kota");
            }
            mTextView.setVisibility(impl.visible());
        }

    }



    public void takePhoto() {
        log.i("takePhoto");
        isPreviewActive = !isPreviewActive;
        if(!isPreviewActive){
            nextRandomCat();
        }
        updateMode();
    }




    /*@
    requires mSurfaceView != null;
    @*/
    public void surfaceChanged() {
        log.i("surfaceChanged");
        if (camera != null) {
            log.i("Changed surface!");
            camera.setPreviewSize(mSurfaceView.getWidth(), mSurfaceView.getHeight());
            updateMode();
        }

    }

    public void surfaceDestroyed() {
        log.i("surfaceDestroyed");
        if (camera != null) {
            camera.stopPreview();
        }
    }

    public void onDestroy() {
        log.i("onDestroy");
        ensureEverythingDestroyed();
    }

    /*@
    requires impl != null;
    ensures mSurfaceView != null;
    ensures mTextView != null;
    @*/
    public void onCreate() {
        log.i("onCreate");
        ensureEverythingWorks();
    }

    public void onStop() {
        log.i("onStop");
        ensureEverythingDestroyed();
    }

    public void surfaceCreated() {
        log.i("surfaceCreated");
    }

    public void onPause() {
        log.i("onPause");
        ensureEverythingDestroyed();
    }

    public void onResume() {
        log.i("onResume");
        ensureEverythingWorks();
    }

}
