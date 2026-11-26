package io.github.zensu357.camswap;

import android.graphics.ImageFormat;
import android.media.Image;
import android.media.ImageReader;
import android.os.Handler;
import android.view.Surface;

import java.nio.ByteBuffer;

/**
 * Takes the camera's real YUV stream in place of one app ImageReader. While the real camera is
 * selected every frame goes to the {@link Sink}, which copies it into the app's reader; otherwise
 * frames are dropped so the fake-frame pumps stay the reader's only producer. Because the relay
 * has the app reader's size and format, the capture session keeps the stream the app asked for.
 */
final class YuvSourceRelay implements ImageReader.OnImageAvailableListener {
    private static final int MAX_IMAGES = 3;

    interface Sink {
        /** Called on the relay thread; {@code frame} is closed once this returns. */
        void onRealFrame(Image frame);
    }

    private final ImageReader reader;
    private final Sink sink;
    private volatile boolean released;

    /**
     * Creating the reader goes through CamSwap's own ImageReader hooks, so callers must mark
     * this as an internal reader before constructing it.
     */
    YuvSourceRelay(int width, int height, Handler handler, Sink sink) {
        this.sink = sink;
        reader = ImageReader.newInstance(width, height, ImageFormat.YUV_420_888, MAX_IMAGES);
        reader.setOnImageAvailableListener(this, handler);
    }

    Surface getSurface() {
        return reader.getSurface();
    }

    @Override
    public void onImageAvailable(ImageReader source) {
        Image image = null;
        try {
            // Always drain, otherwise the camera stalls this stream once MAX_IMAGES are queued.
            image = source.acquireLatestImage();
            if (image != null && !released && SwitchablePreview.useOriginalCamera()) {
                sink.onRealFrame(image);
            }
        } catch (IllegalStateException ignored) {
            // Reader closed while a frame was in flight.
        } finally {
            if (image != null) {
                try {
                    image.close();
                } catch (Throwable ignored) {
                }
            }
        }
    }

    /** Only call once the camera no longer streams into {@link #getSurface()}. */
    void release() {
        released = true;
        try {
            reader.setOnImageAvailableListener(null, null);
            reader.close();
        } catch (Throwable ignored) {
        }
    }

    /** Copies a YUV_420_888 frame between images whose planes may use different strides. */
    static void copyFrame(Image src, Image dst) {
        int width = Math.min(src.getWidth(), dst.getWidth());
        int height = Math.min(src.getHeight(), dst.getHeight());
        Image.Plane[] in = src.getPlanes();
        Image.Plane[] out = dst.getPlanes();
        byte[] row = new byte[width];
        for (int plane = 0; plane < 3; plane++) {
            int planeWidth = plane == 0 ? width : (width + 1) / 2;
            int planeHeight = plane == 0 ? height : (height + 1) / 2;
            copyPlane(in[plane], out[plane], planeWidth, planeHeight, row);
        }
    }

    private static void copyPlane(Image.Plane src, Image.Plane dst, int width, int height, byte[] row) {
        ByteBuffer in = src.getBuffer();
        ByteBuffer out = dst.getBuffer();
        int inRowStride = src.getRowStride();
        int outRowStride = dst.getRowStride();
        int inPixelStride = src.getPixelStride();
        int outPixelStride = dst.getPixelStride();
        if (inPixelStride == 1 && outPixelStride == 1) {
            for (int y = 0; y < height; y++) {
                in.position(y * inRowStride);
                in.get(row, 0, width);
                out.position(y * outRowStride);
                out.put(row, 0, width);
            }
            return;
        }
        // Interleaved chroma (NV12/NV21) can differ in U/V order between the two images, so
        // copy sample by sample instead of whole rows.
        for (int y = 0; y < height; y++) {
            int inRow = y * inRowStride;
            int outRow = y * outRowStride;
            for (int x = 0; x < width; x++) {
                out.put(outRow + x * outPixelStride, in.get(inRow + x * inPixelStride));
            }
        }
    }
}
