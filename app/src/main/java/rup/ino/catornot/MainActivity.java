package rup.ino.catornot;

import android.graphics.Bitmap;
import android.graphics.BitmapFactory;
import android.graphics.Canvas;
import android.hardware.Camera;
import android.os.Bundle;
import android.os.Handler;
import android.os.Looper;
import android.support.annotation.NonNull;
import android.support.design.widget.BottomNavigationView;
import android.support.v7.app.AppCompatActivity;
import android.util.Log;
import android.view.MenuItem;
import android.view.Surface;
import android.view.SurfaceHolder;
import android.view.SurfaceView;
import android.view.View;
import android.widget.TextView;

public class MainActivity extends AppCompatActivity implements SurfaceHolder.Callback {

    private TextView mTextView;
    private SurfaceView mSurfaceView;
    private SurfaceHolder mHolder;
    private static Camera camera;
    private static boolean isPreviewActive = false;

    private static void stopPreview() {
        if (camera != null)
            camera.stopPreview();
        isPreviewActive = false;
        Log.i("Action","Stopped preview!");
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
            Log.i("Action","Freed preview!");
        }
    }

    private int getActivityOrientation() {
        switch (getWindowManager().getDefaultDisplay()
                .getRotation()) {
            case Surface.ROTATION_0:
                return 0;
            case Surface.ROTATION_90:
                return 90;
            case Surface.ROTATION_180:
                return 180;
            case Surface.ROTATION_270:
                return 270;
        }
        throw new RuntimeException("If you got here then something is terribly wrong!");
    }

    private int getCameraOrientation() {
        int activityOrient = getActivityOrientation();
        Camera.CameraInfo cameraInfo = new Camera.CameraInfo();
        Camera.getCameraInfo(0, cameraInfo);
        if (cameraInfo.facing == Camera.CameraInfo.CAMERA_FACING_FRONT) {
            return (360 - (cameraInfo.orientation + activityOrient) % 360) % 360;  // compensate the mirror
        } else {  // back-facing
            return (cameraInfo.orientation - activityOrient + 360) % 360;
        }
    }
    private static void startPreview() {
        if (camera == null) throw new RuntimeException("You should not be here!");
        camera.setOneShotPreviewCallback(new Camera.PreviewCallback() {
            @Override
            public void onPreviewFrame(byte[] data, Camera camera) {
                isPreviewActive = true;
                Log.i("Action","Started preview!");
            }
        });
        camera.startPreview();

    }
    private boolean safeCameraOpen(int id) {
        try {
            stopPreviewAndFreeCamera();
            camera = Camera.open(id);
            if (camera == null) return false;
            camera.setDisplayOrientation(getCameraOrientation());
            camera.setPreviewDisplay(mHolder);

            startPreview();
            Log.i("Action","Created camera!");
        } catch (Exception e) {
            Log.e(getString(R.string.app_name), "failed to open Camera");
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
        Log.i("Action","Going to preview mode!");
        mTextView.setVisibility(View.INVISIBLE);
    }

    private void startPhotoMode() {
        if (camera == null)
            throw new RuntimeException("You shouldn't get here!");
        Log.i("Action","Going to photo mode!");
        stopPreview();
        if (Math.random() > 0.5) {
            Log.i("Cat", "No cat!");
            mTextView.setText("Nie ma kota");
        } else {
            Log.i("Cat", "Is cat!");
            mTextView.setText("Jest kot");
        }
        mTextView.setVisibility(View.VISIBLE);
    }

    private BottomNavigationView.OnNavigationItemSelectedListener mOnNavigationItemSelectedListener
            = new BottomNavigationView.OnNavigationItemSelectedListener() {

        @Override
        public boolean onNavigationItemSelected(@NonNull MenuItem item) {
            switch (item.getItemId()) {
                case R.id.navigation_home:
                    return true;
                case R.id.take_photo:
                    Log.i("Action","Taking photo!");
                    if (!isPreviewActive) {
                        startPreviewMode();
                    } else {
                        startPhotoMode();
                    }
                    return true;
                case R.id.navigation_notifications:
                    return true;
            }
            return false;
        }
    };

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        setContentView(R.layout.activity_main);

        mSurfaceView = (SurfaceView) findViewById(R.id.surfaceView);
        mTextView = (TextView) findViewById(R.id.textView);
        mHolder = mSurfaceView.getHolder();
        mHolder.addCallback(this);
//        mHolder.setType(SurfaceHolder.SURFACE_TYPE_PUSH_BUFFERS);

        new Handler().postDelayed(new Runnable() {
            public void run() {
                safeCameraOpen(0);
            }
        }, 100);
        BottomNavigationView navigation = (BottomNavigationView) findViewById(R.id.navigation);
        navigation.setOnNavigationItemSelectedListener(mOnNavigationItemSelectedListener);
    }

    @Override
    protected void onResume() {
        super.onResume();
    }

    @Override
    public void surfaceCreated(SurfaceHolder holder) {

    }

    @Override
    public void surfaceChanged(SurfaceHolder holder, int format, int width, int height) {
        if (camera != null) {
            Log.i("Action","Changed surface!");
            camera.getParameters().setPreviewSize(mSurfaceView.getWidth(), mSurfaceView.getHeight());
            // Important: Call startPreview() to start updating the preview surface.
            // Preview must be started before you can take a picture.
            startPreview();
        }

    }

    @Override
    public void surfaceDestroyed(SurfaceHolder holder) {
        if (camera != null) {
            // Call stopPreview() to stop updating the preview surface.
            stopPreview();
        }
    }

    @Override
    protected void onDestroy() {
        super.onDestroy();
        stopPreviewAndFreeCamera();
    }


}
