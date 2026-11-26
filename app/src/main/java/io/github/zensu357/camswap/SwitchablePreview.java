package io.github.zensu357.camswap;

import android.graphics.SurfaceTexture;
import android.opengl.EGL14;
import android.opengl.EGLConfig;
import android.opengl.EGLContext;
import android.opengl.EGLDisplay;
import android.opengl.EGLSurface;
import android.opengl.GLES11Ext;
import android.opengl.GLES20;
import android.opengl.Matrix;
import android.os.Handler;
import android.os.HandlerThread;
import android.view.Surface;

import java.nio.FloatBuffer;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import io.github.zensu357.camswap.utils.LogUtil;
import io.github.zensu357.camswap.utils.VideoManager;

/**
 * Owns an app preview Surface so the camera source can change without reconfiguring the
 * capture session. The camera always renders into {@link #getCameraSurface()}, the media
 * pipeline into {@link #getMediaSurface()}, and only frames from the currently selected source
 * are drawn to the app's Surface. Both inputs are sized like the app's Surface so the camera
 * stream keeps the size the app configured.
 */
class SwitchablePreview {
    private static final String NATIVE_LIBRARY = "camswap-native-hook";
    private static final long INIT_TIMEOUT_MS = 3000L;
    private static final long RELEASE_TIMEOUT_MS = 1000L;
    private static final Object NATIVE_LOCK = new Object();
    private static Boolean nativeLoaded;

    private final Surface output;
    private final String tag;
    private final HandlerThread thread;
    private final Handler handler;

    private EGLDisplay eglDisplay = EGL14.EGL_NO_DISPLAY;
    private EGLContext eglContext = EGL14.EGL_NO_CONTEXT;
    private EGLSurface eglSurface = EGL14.EGL_NO_SURFACE;
    private int program;
    private int positionHandle;
    private int texCoordHandle;
    private int stMatrixHandle;
    private int rotMatrixHandle;
    private int ambientIntensityHandle;
    private FloatBuffer vertices;
    private FloatBuffer texCoords;

    private int cameraTextureId;
    private int mediaTextureId;
    private SurfaceTexture cameraTexture;
    private SurfaceTexture mediaTexture;
    private Surface cameraSurface;
    private Surface mediaSurface;

    private final float[] textureMatrix = new float[16];
    private final float[] drawMatrix = new float[16];
    private final float[] identity = new float[16];
    /** NATIVE_WINDOW_TRANSFORM currently applied to the app's Surface. */
    private int appliedTransform;
    /** Source of the last frame drawn; null until the first frame. */
    private Boolean lastDrawnCamera;
    private volatile boolean released;
    private boolean releaseRequested;

    /** Global switch shared by Camera1, Camera2, ImageReader and microphone hooks. */
    static boolean useOriginalCamera() {
        return VideoManager.getConfig().getBoolean(ConfigManager.KEY_USE_ORIGINAL_CAMERA, false);
    }

    /**
     * Takes over {@code output} as its only producer. Returns null when the GL bridge cannot be
     * set up (e.g. the Surface is not GPU-renderable); callers must then keep the camera off the
     * real output so the app never sees camera frames unintentionally.
     */
    static SwitchablePreview create(Surface output) {
        if (output == null || !output.isValid()) {
            return null;
        }
        SwitchablePreview preview = new SwitchablePreview(output);
        if (preview.start()) {
            return preview;
        }
        preview.release();
        return null;
    }

    private SwitchablePreview(Surface output) {
        this.output = output;
        this.tag = Integer.toHexString(System.identityHashCode(output));
        thread = new HandlerThread("CS-SwitchablePreview");
        thread.start();
        handler = new Handler(thread.getLooper());
        Matrix.setIdentityM(identity, 0);
    }

    Surface getCameraSurface() {
        return cameraSurface;
    }

    Surface getMediaSurface() {
        return mediaSurface;
    }

    private boolean start() {
        final boolean[] ok = { false };
        CountDownLatch latch = new CountDownLatch(1);
        handler.post(() -> {
            try {
                ok[0] = initOnGlThread();
            } catch (Throwable t) {
                LogUtil.log("【CS】【预览桥接】[" + tag + "] 初始化失败: " + t);
            } finally {
                latch.countDown();
            }
        });
        try {
            if (!latch.await(INIT_TIMEOUT_MS, TimeUnit.MILLISECONDS)) {
                LogUtil.log("【CS】【预览桥接】[" + tag + "] 初始化超时");
                return false;
            }
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return false;
        }
        return ok[0];
    }

    private boolean initOnGlThread() {
        eglDisplay = EGL14.eglGetDisplay(EGL14.EGL_DEFAULT_DISPLAY);
        int[] version = new int[2];
        if (eglDisplay == EGL14.EGL_NO_DISPLAY || !EGL14.eglInitialize(eglDisplay, version, 0, version, 1)) {
            throw new IllegalStateException("eglInitialize failed");
        }
        int[] configAttribs = {
                EGL14.EGL_RED_SIZE, 8, EGL14.EGL_GREEN_SIZE, 8, EGL14.EGL_BLUE_SIZE, 8,
                EGL14.EGL_ALPHA_SIZE, 8,
                EGL14.EGL_RENDERABLE_TYPE, EGL14.EGL_OPENGL_ES2_BIT,
                EGL14.EGL_SURFACE_TYPE, EGL14.EGL_WINDOW_BIT,
                EGL14.EGL_NONE };
        EGLConfig[] configs = new EGLConfig[1];
        int[] numConfigs = new int[1];
        if (!EGL14.eglChooseConfig(eglDisplay, configAttribs, 0, configs, 0, 1, numConfigs, 0)
                || numConfigs[0] == 0) {
            throw new IllegalStateException("eglChooseConfig failed");
        }
        eglContext = EGL14.eglCreateContext(eglDisplay, configs[0], EGL14.EGL_NO_CONTEXT,
                new int[] { EGL14.EGL_CONTEXT_CLIENT_VERSION, 2, EGL14.EGL_NONE }, 0);
        if (eglContext == EGL14.EGL_NO_CONTEXT) {
            throw new IllegalStateException("eglCreateContext failed");
        }
        // Fails if another producer (e.g. a camera stream) is already connected to the output.
        eglSurface = EGL14.eglCreateWindowSurface(eglDisplay, configs[0], output,
                new int[] { EGL14.EGL_NONE }, 0);
        if (eglSurface == EGL14.EGL_NO_SURFACE) {
            throw new IllegalStateException("eglCreateWindowSurface failed: " + EGL14.eglGetError());
        }
        if (!EGL14.eglMakeCurrent(eglDisplay, eglSurface, eglSurface, eglContext)) {
            throw new IllegalStateException("eglMakeCurrent failed");
        }
        int[] width = new int[1];
        int[] height = new int[1];
        EGL14.eglQuerySurface(eglDisplay, eglSurface, EGL14.EGL_WIDTH, width, 0);
        EGL14.eglQuerySurface(eglDisplay, eglSurface, EGL14.EGL_HEIGHT, height, 0);
        // A SurfaceHolder without allocated buffers reports 1x1; such a size would also become
        // the camera stream size, so treat it as unusable.
        if (width[0] <= 1 || height[0] <= 1) {
            throw new IllegalStateException("output too small: " + width[0] + "x" + height[0]);
        }

        program = createProgram();
        positionHandle = GLES20.glGetAttribLocation(program, "aPosition");
        texCoordHandle = GLES20.glGetAttribLocation(program, "aTextureCoord");
        stMatrixHandle = GLES20.glGetUniformLocation(program, "uSTMatrix");
        rotMatrixHandle = GLES20.glGetUniformLocation(program, "uRotMatrix");
        ambientIntensityHandle = GLES20.glGetUniformLocation(program, "uAmbientIntensity");
        vertices = GLHelper.createFloatBuffer(GLHelper.VERTICES);
        texCoords = GLHelper.createFloatBuffer(GLHelper.TEX_COORDS);

        cameraTextureId = createExternalTexture();
        mediaTextureId = createExternalTexture();
        cameraTexture = new SurfaceTexture(cameraTextureId);
        mediaTexture = new SurfaceTexture(mediaTextureId);
        cameraTexture.setDefaultBufferSize(width[0], height[0]);
        mediaTexture.setDefaultBufferSize(width[0], height[0]);
        cameraTexture.setOnFrameAvailableListener(st -> onFrame(true), handler);
        mediaTexture.setOnFrameAvailableListener(st -> onFrame(false), handler);
        cameraSurface = new Surface(cameraTexture);
        mediaSurface = new Surface(mediaTexture);
        LogUtil.log("【CS】【预览桥接】[" + tag + "] 已接管预览 " + width[0] + "x" + height[0]
                + " (当前来源: " + (useOriginalCamera() ? "原始相机" : "虚拟视频") + ")");
        return true;
    }

    private static int createProgram() {
        int vertex = GLHelper.loadShader(GLES20.GL_VERTEX_SHADER, GLHelper.VERTEX_SHADER);
        int fragment = GLHelper.loadShader(GLES20.GL_FRAGMENT_SHADER, GLHelper.FRAGMENT_SHADER);
        int program = GLES20.glCreateProgram();
        GLES20.glAttachShader(program, vertex);
        GLES20.glAttachShader(program, fragment);
        GLES20.glLinkProgram(program);
        int[] status = new int[1];
        GLES20.glGetProgramiv(program, GLES20.GL_LINK_STATUS, status, 0);
        if (status[0] != GLES20.GL_TRUE) {
            String error = GLES20.glGetProgramInfoLog(program);
            GLES20.glDeleteProgram(program);
            throw new IllegalStateException("program link failed: " + error);
        }
        return program;
    }

    private static int createExternalTexture() {
        int[] textures = new int[1];
        GLES20.glGenTextures(1, textures, 0);
        GLES20.glBindTexture(GLES11Ext.GL_TEXTURE_EXTERNAL_OES, textures[0]);
        GLES20.glTexParameteri(GLES11Ext.GL_TEXTURE_EXTERNAL_OES, GLES20.GL_TEXTURE_MIN_FILTER, GLES20.GL_LINEAR);
        GLES20.glTexParameteri(GLES11Ext.GL_TEXTURE_EXTERNAL_OES, GLES20.GL_TEXTURE_MAG_FILTER, GLES20.GL_LINEAR);
        GLES20.glTexParameteri(GLES11Ext.GL_TEXTURE_EXTERNAL_OES, GLES20.GL_TEXTURE_WRAP_S, GLES20.GL_CLAMP_TO_EDGE);
        GLES20.glTexParameteri(GLES11Ext.GL_TEXTURE_EXTERNAL_OES, GLES20.GL_TEXTURE_WRAP_T, GLES20.GL_CLAMP_TO_EDGE);
        return textures[0];
    }

    /**
     * Every frame is latched so neither producer stalls on a full queue; only frames from the
     * selected source reach the app, so a switch takes effect on the next frame.
     */
    private void onFrame(boolean fromCamera) {
        if (released) {
            return;
        }
        try {
            if (!EGL14.eglMakeCurrent(eglDisplay, eglSurface, eglSurface, eglContext)) {
                return;
            }
            SurfaceTexture texture = fromCamera ? cameraTexture : mediaTexture;
            texture.updateTexImage();
            if (fromCamera != useOriginalCamera()) {
                return;
            }
            if (!output.isValid()) {
                LogUtil.log("【CS】【预览桥接】[" + tag + "] 应用预览 Surface 已失效，停止输出");
                released = true;
                return;
            }
            texture.getTransformMatrix(textureMatrix);
            draw(fromCamera ? cameraTextureId : mediaTextureId, resolveDrawMatrix(fromCamera));
            if (!EGL14.eglSwapBuffers(eglDisplay, eglSurface)) {
                int error = EGL14.eglGetError();
                LogUtil.log("【CS】【预览桥接】[" + tag + "] eglSwapBuffers 失败: " + error);
                if (error == EGL14.EGL_BAD_SURFACE || error == EGL14.EGL_BAD_NATIVE_WINDOW) {
                    released = true;
                }
                return;
            }
            if (lastDrawnCamera == null || lastDrawnCamera != fromCamera) {
                lastDrawnCamera = fromCamera;
                LogUtil.log("【CS】【预览桥接】[" + tag + "] 输出切换为: " + (fromCamera ? "原始相机" : "虚拟视频"));
            }
        } catch (Throwable t) {
            LogUtil.log("【CS】【预览桥接】[" + tag + "] 绘制失败: " + t);
        }
    }

    /**
     * Camera buffers carry an orientation transform that the app's consumer would normally
     * apply itself. Forward that transform to the output and draw only the crop, so the app
     * sees the same buffers as with a direct camera connection. Media frames are upright.
     */
    private float[] resolveDrawMatrix(boolean fromCamera) {
        int transform = 0;
        float[] matrix = textureMatrix;
        if (fromCamera && isNativeLoaded()) {
            int code = BufferTransform.fromMatrix(textureMatrix);
            if (code > 0) {
                BufferTransform.removeOrientation(textureMatrix, code, drawMatrix);
                matrix = drawMatrix;
                transform = code;
            }
        }
        if (transform != appliedTransform) {
            if (applyBuffersTransform(output, transform)) {
                appliedTransform = transform;
            } else {
                // Without the transform the orientation has to be baked into the pixels instead.
                return textureMatrix;
            }
        }
        return matrix;
    }

    private void draw(int textureId, float[] matrix) {
        GLES20.glClearColor(0f, 0f, 0f, 1f);
        GLES20.glClear(GLES20.GL_COLOR_BUFFER_BIT);
        GLES20.glUseProgram(program);
        GLES20.glActiveTexture(GLES20.GL_TEXTURE0);
        GLES20.glBindTexture(GLES11Ext.GL_TEXTURE_EXTERNAL_OES, textureId);
        GLES20.glUniformMatrix4fv(stMatrixHandle, 1, false, matrix, 0);
        GLES20.glUniformMatrix4fv(rotMatrixHandle, 1, false, identity, 0);
        if (ambientIntensityHandle >= 0) {
            GLES20.glUniform1f(ambientIntensityHandle, 0f);
        }
        vertices.position(0);
        GLES20.glEnableVertexAttribArray(positionHandle);
        GLES20.glVertexAttribPointer(positionHandle, 2, GLES20.GL_FLOAT, false, 0, vertices);
        texCoords.position(0);
        GLES20.glEnableVertexAttribArray(texCoordHandle);
        GLES20.glVertexAttribPointer(texCoordHandle, 2, GLES20.GL_FLOAT, false, 0, texCoords);
        GLES20.glDrawArrays(GLES20.GL_TRIANGLE_STRIP, 0, 4);
    }

    /** Disconnects from the app's Surface so the app or a later session can use it again. */
    synchronized void release() {
        if (releaseRequested) {
            return;
        }
        releaseRequested = true;
        released = true;
        CountDownLatch latch = new CountDownLatch(1);
        boolean posted = handler.post(() -> {
            try {
                releaseOnGlThread();
            } finally {
                latch.countDown();
            }
        });
        if (posted) {
            try {
                latch.await(RELEASE_TIMEOUT_MS, TimeUnit.MILLISECONDS);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }
        thread.quitSafely();
    }

    private void releaseOnGlThread() {
        if (appliedTransform != 0 && output.isValid()) {
            applyBuffersTransform(output, 0);
        }
        if (cameraTexture != null) cameraTexture.setOnFrameAvailableListener(null);
        if (mediaTexture != null) mediaTexture.setOnFrameAvailableListener(null);
        if (cameraSurface != null) cameraSurface.release();
        if (mediaSurface != null) mediaSurface.release();
        if (cameraTexture != null) cameraTexture.release();
        if (mediaTexture != null) mediaTexture.release();
        if (eglDisplay != EGL14.EGL_NO_DISPLAY) {
            if (eglContext != EGL14.EGL_NO_CONTEXT && eglSurface != EGL14.EGL_NO_SURFACE
                    && EGL14.eglMakeCurrent(eglDisplay, eglSurface, eglSurface, eglContext)) {
                if (program != 0) GLES20.glDeleteProgram(program);
                GLES20.glDeleteTextures(2, new int[] { cameraTextureId, mediaTextureId }, 0);
            }
            EGL14.eglMakeCurrent(eglDisplay, EGL14.EGL_NO_SURFACE, EGL14.EGL_NO_SURFACE, EGL14.EGL_NO_CONTEXT);
            if (eglSurface != EGL14.EGL_NO_SURFACE) EGL14.eglDestroySurface(eglDisplay, eglSurface);
            if (eglContext != EGL14.EGL_NO_CONTEXT) EGL14.eglDestroyContext(eglDisplay, eglContext);
        }
        eglSurface = EGL14.EGL_NO_SURFACE;
        eglContext = EGL14.EGL_NO_CONTEXT;
        eglDisplay = EGL14.EGL_NO_DISPLAY;
        LogUtil.log("【CS】【预览桥接】[" + tag + "] 已释放");
    }

    private static boolean isNativeLoaded() {
        synchronized (NATIVE_LOCK) {
            if (nativeLoaded == null) {
                try {
                    System.loadLibrary(NATIVE_LIBRARY);
                    nativeLoaded = true;
                } catch (Throwable t) {
                    nativeLoaded = false;
                    LogUtil.log("【CS】【预览桥接】native 库不可用，相机方向将直接绘制进画面: " + t);
                }
            }
            return nativeLoaded;
        }
    }

    private static boolean applyBuffersTransform(Surface surface, int transform) {
        if (!isNativeLoaded()) {
            return transform == 0;
        }
        try {
            return nativeSetBuffersTransform(surface, transform);
        } catch (Throwable t) {
            return false;
        }
    }

    // Implemented in cpp/buffer_transform.cpp.
    private static native boolean nativeSetBuffersTransform(Surface surface, int transform);
}
