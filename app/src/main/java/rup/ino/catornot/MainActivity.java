package rup.ino.catornot;

import android.Manifest;
import android.app.AlertDialog;
import android.content.pm.PackageManager;
import android.hardware.Camera;
import android.os.Bundle;
import android.os.Handler;
import android.support.annotation.NonNull;
import android.support.design.widget.BottomNavigationView;
import android.support.v4.app.ActivityCompat;
import android.support.v4.content.ContextCompat;
import android.support.v7.app.AppCompatActivity;
import android.util.Log;
import android.view.MenuItem;
import android.view.Surface;
import android.view.SurfaceHolder;
import android.view.SurfaceView;
import android.view.View;
import android.widget.ProgressBar;
import android.widget.TextView;

import java.io.IOException;

public class MainActivity extends AppCompatActivity implements SurfaceHolder.Callback {

    class MainCamera implements MainActivitySkeleton.CameraSkeleton {
        Camera c;

        MainCamera(Camera c) {
            this.c = c;
        }

        @Override
        public void stopPreview() {
            c.stopPreview();
        }

        @Override
        public void release() {
            c.release();
        }

        @Override
        public void startPreview() {
            c.startPreview();
        }

        @Override
        public void reconnect() throws IOException {
            c.reconnect();
        }

        @Override
        public void setOneShotPreviewCallback(final MainActivitySkeleton.PreviewCallback action) {
            c.setOneShotPreviewCallback(new Camera.PreviewCallback() {
                @Override
                public void onPreviewFrame(byte[] data, Camera camera) {
                    action.onPreviewFrame(data);
                }
            });
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

        @Override
        public void setDisplayOrientation() throws IOException {
            c.setDisplayOrientation(getCameraOrientation());

        }

        @Override
        public void setPreviewDisplay(MainActivitySkeleton.SurfaceHolder holder) throws IOException {
            c.setPreviewDisplay(((MainSurfaceHolder) holder).h);
        }


        @Override
        public void setPreviewSize(int width, int height) {
            c.getParameters().setPreviewSize(width, height);
        }
    }

    static class MainTextView implements MainActivitySkeleton.TextView {

        final TextView tv;

        MainTextView(TextView tv) {
            this.tv = tv;
        }

        @Override
        public void setText(String txt) {
            tv.setText(txt);
        }

        @Override
        public void setVisibility(int v) {
            tv.setVisibility(v);
        }
    }

    class MainSurfaceHolder implements MainActivitySkeleton.SurfaceHolder {

        private final SurfaceHolder h;

        public MainSurfaceHolder(SurfaceHolder holder) {
            h = holder;
        }

        @Override
        public void addCallback() {
            h.addCallback(MainActivity.this);
        }

        @Override
        public void removeCallback() {
            h.removeCallback(MainActivity.this);
        }
    }

    class MainSurfaceView implements MainActivitySkeleton.SurfaceView {

        final SurfaceView sv;

        MainSurfaceView(SurfaceView sv) {
            this.sv = sv;
        }

        @Override
        public int getWidth() {
            return sv.getWidth();
        }

        @Override
        public int getHeight() {
            return sv.getHeight();
        }

        @Override
        public MainActivitySkeleton.SurfaceHolder getHolder() {
            return new MainSurfaceHolder(sv.getHolder());
        }
    }

    class MainProgressBar implements MainActivitySkeleton.ProgressBar {
        private final ProgressBar pb;

        MainProgressBar(ProgressBar progressBar) {
            pb = progressBar;

        }

        @Override
        public void setVisibility(int v) {
            pb.setVisibility(v);

        }

        @Override
        public void setProgress(int progress) {
            pb.setProgress(progress);
        }

        @Override
        public int getMax() {
            return pb.getMax();
        }

        @Override
        public int getProgress() {
            return pb.getProgress();
        }

        @Override
        public void post(Runnable runnable) {
            pb.post(runnable);
        }

    }

    class MainHandler implements MainActivitySkeleton.Handler {
        private final Handler h;

        MainHandler(Handler handler) {
            h = handler;

        }

        @Override
        public void post(Runnable runnable) {
            h.post(runnable);
        }

        @Override
        public void postDelayed(Runnable runnable, long delayMilis) {
            h.postDelayed(runnable, delayMilis);
        }
    }

    class MainImpl implements MainActivitySkeleton.Impl {

        @Override
        public MainActivitySkeleton.CameraSkeleton cameraOpen(int id) {
            Camera c = Camera.open(id);
            if (c == null) return null;
            return new MainCamera(c);
        }

        @Override
        public int invisible() {
            return View.INVISIBLE;
        }

        @Override
        public MainActivitySkeleton.SurfaceView findSurfaceView() {
            return new MainSurfaceView((SurfaceView) findViewById(R.id.surfaceView));
        }

        @Override
        public MainActivitySkeleton.TextView findTextView() {
            return new MainTextView((TextView) findViewById(R.id.textView));
        }

        @Override
        public MainActivitySkeleton.ProgressBar findProgressBar() {
            return new MainProgressBar((ProgressBar) findViewById(R.id.progressBar));
        }

        @Override
        public int visible() {
            return View.VISIBLE;
        }

        @Override
        public MainActivitySkeleton.Handler getHandler() {
            return new MainHandler(new Handler());
        }

        @Override
        public void checkPermissions() {
            if (ContextCompat.checkSelfPermission(MainActivity.this, Manifest.permission.CAMERA)
                    != PackageManager.PERMISSION_GRANTED) {
                ActivityCompat.requestPermissions(MainActivity.this, new String[]{Manifest.permission.CAMERA}, 1);
            } else {
                skeleton.permissionGranted();
            }
        }

        @Override
        public void attachCallbacks() {
            BottomNavigationView navigation = findViewById(R.id.navigation);
            navigation.setOnNavigationItemSelectedListener(mOnNavigationItemSelectedListener);
        }

        @Override
        public void showDialog(String s) {
            AlertDialog.Builder builder = new AlertDialog.Builder(MainActivity.this);
            builder.setMessage(s).setNeutralButton("OK", null);
            builder.create().show();
        }

        @Override
        public void sleep(long milis) {
            try {
                Thread.sleep(milis);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
    }

    static class MainLog implements MainActivitySkeleton.Log {
        @Override
        public void i(String message) {
            Log.i("Action", message);
        }

        @Override
        public void e(String error) {
            Log.e("Action", error);
        }
    }

    private final MainImpl impl = new MainImpl();
    private final MainActivitySkeleton skeleton = new MainActivitySkeleton(new MainLog(), impl);


    private BottomNavigationView.OnNavigationItemSelectedListener mOnNavigationItemSelectedListener
            = new BottomNavigationView.OnNavigationItemSelectedListener() {

        @Override
        public boolean onNavigationItemSelected(@NonNull MenuItem item) {
            switch (item.getItemId()) {
                case R.id.navigation_home:
                    return true;
                case R.id.take_photo:
                    skeleton.takePhoto();
                    return true;
                case R.id.navigation_notifications:
                    return true;
            }
            return false;
        }
    };

    @Override
    public void onRequestPermissionsResult(int requestCode, @NonNull String[] permissions, @NonNull int[] grantResults) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults);
        if (grantResults.length > 0
                && grantResults[0] == PackageManager.PERMISSION_GRANTED) {
            skeleton.permissionGranted();
        } else {
            finish();
        }
    }

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        setContentView(R.layout.activity_main);
        skeleton.onCreate();

    }

    @Override
    protected void onResume() {
        super.onResume();
        skeleton.onResume();
    }

    @Override
    protected void onPause() {
        super.onPause();
        skeleton.onPause();
    }

    @Override
    public void surfaceCreated(SurfaceHolder holder) {
        skeleton.surfaceCreated();
    }

    @Override
    public void surfaceChanged(SurfaceHolder holder, int format, int width, int height) {
        skeleton.surfaceChanged();
    }

    @Override
    public void surfaceDestroyed(SurfaceHolder holder) {
        skeleton.surfaceDestroyed();
    }

    @Override
    protected void onStop() {
        super.onStop();
        skeleton.onStop();
    }

    @Override
    protected void onDestroy() {
        super.onDestroy();
        skeleton.onDestroy();
    }


}
