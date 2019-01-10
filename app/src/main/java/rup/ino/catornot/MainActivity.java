package rup.ino.catornot;

import android.Manifest;
import android.app.AlertDialog;
import android.content.pm.PackageManager;
import android.graphics.Color;
import android.hardware.Camera;
import android.os.Bundle;
import android.os.Handler;
import android.support.annotation.NonNull;
import android.support.v4.app.ActivityCompat;
import android.support.v4.content.ContextCompat;
import android.support.v7.app.AppCompatActivity;
import android.util.Log;
import android.view.Surface;
import android.view.SurfaceHolder;
import android.view.SurfaceView;
import android.view.View;
import android.widget.ImageButton;
import android.widget.LinearLayout;
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

        @Override
        public void setTextNoCat() {
            tv.setText("Nie ma kota");
            tv.setBackgroundColor(Color.parseColor("#F44336"));
        }

        @Override
        public void setTextIsCat() {
            tv.setText("Jest kot");
            tv.setBackgroundColor(Color.parseColor("#8BC34A"));
        }

        MainTextView(TextView tv) {
            this.tv = tv;
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

    }

    class MainHandler extends MainActivitySkeleton.Handler {
        private final Handler h;

        MainHandler(Handler handler) {
            h = handler;

        }

        @Override
        public void postDelayedCameraOpener(final MainActivitySkeleton s, final long delayMilis) {

            h.postDelayed(new Runnable() {
                @Override
                public void run() {
                    MainHandler.super.postDelayedCameraOpener(s, delayMilis);
                }
            },delayMilis);
        }

        @Override
        public void postProgressFinalizer(final MainActivitySkeleton s) {
            h.post(new Runnable() {
                @Override
                public void run() {
                    MainHandler.super.postProgressFinalizer(s);
                }
            });
        }

        @Override
        public void postProgressUpdater(final MainActivitySkeleton s, final int progress) {
            h.post(new Runnable() {
                @Override
                public void run() {
                    MainHandler.super.postProgressUpdater(s, progress);
                }
            });

        }

        @Override
        public void startProgressBarThread(final MainActivitySkeleton s) {
            new Thread(new Runnable() {
                @Override
                public void run() {
                    MainHandler.super.startProgressBarThread(s);
                }
            }).start();
        }
    }

    static class MainMenuItem implements MainActivitySkeleton.MenuItem{
        private final ImageButton i;
        private final LinearLayout l;
        private MainMenuItem(ImageButton item, LinearLayout layout){
            i = item;
            l = layout;

        }

        @Override
        public void setTakePhotoText() {

            i.setImageResource(R.drawable.ic_photo_camera_white_24dp);
            i.setBackgroundColor(Color.parseColor("#696969"));
            l.setBackgroundColor(Color.parseColor("#696969"));
//            i.setText("Zrób zdjęcie");
        }

        @Override
        public void setTakeNextPhotoText() {

            i.setImageResource(R.drawable.ic_refresh_black_24dp);
            i.setBackgroundColor(Color.parseColor("#00cdf4"));
            l.setBackgroundColor(Color.parseColor("#009eba"));
//            i.setText("Zrób kolejne zdjęcie");
        }

        @Override
        public void setEnabled(boolean t){
            i.setEnabled(t);
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
        public MainActivitySkeleton.MenuItem findTakePhotoButton() {
            return new MainMenuItem((ImageButton) findViewById(R.id.navigation), (LinearLayout) findViewById(R.id.linear));
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
        public void attachCallbacks() {
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

        @Override
        public void startThread(final MainActivitySkeleton.Runnable runnable) {
            new Thread(new Runnable() {
                @Override
                public void run() {
                    runnable.run();
                }
            }).start();
        }

        @Override
        public MainActivitySkeleton.PermissionHandler getPermissionHandler() {
            return new MainActivitySkeleton.PermissionHandler(){
                @Override
                void checkPermissions(MainActivitySkeleton skel) {
                    if (ContextCompat.checkSelfPermission(MainActivity.this, Manifest.permission.CAMERA)
                            != PackageManager.PERMISSION_GRANTED) {
                        ActivityCompat.requestPermissions(MainActivity.this, new String[]{Manifest.permission.CAMERA}, 1);
                    } else {
                        skeleton.permissionGranted();
                    }
                }
            };
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

    public void onClickTakePhoto(View view) {
            skeleton.takePhoto();
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
