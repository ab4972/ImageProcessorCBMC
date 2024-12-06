#include "simple_sod.h"
#include <stdlib.h>
#include <string.h>
#undef memcpy
#include <stdint.h>

//memcpy stub from AWS C Common repository
void *memcpy_impl(void *dst, const void *src, size_t n) {
    __CPROVER_precondition(
        __CPROVER_POINTER_OBJECT(dst) != __CPROVER_POINTER_OBJECT(src) ||
            ((const char *)src >= (const char *)dst + n) || ((const char *)dst >= (const char *)src + n),
        "memcpy src/dst overlap");
    __CPROVER_precondition(src != NULL && __CPROVER_r_ok(src, n), "memcpy source region readable");
    __CPROVER_precondition(dst != NULL && __CPROVER_w_ok(dst, n), "memcpy destination region writeable");

    if (n > 0) {
        size_t index;
        __CPROVER_assume(index < n);
        ((uint8_t *)dst)[index] = nondet_uint8_t();
    }
    return dst;
}

void *memcpy(void *dst, const void *src, size_t n) {
    return memcpy_impl(dst, src, n);
}

void *__builtin___memcpy_chk(void *dst, const void *src, __CPROVER_size_t n, __CPROVER_size_t size) {
    (void)size;
    return memcpy_impl(dst, src, n);
}

sod_img sod_make_image(int w, int h, int c) {
    sod_img img = {0};
    __CPROVER_assume(w >= 0 && w <= 4);  // Max width 4
    __CPROVER_assume(h >= 0 && h <= 4);  // Max height 4
    __CPROVER_assume(c >= 1 && c <= 3);  // 1-3 channels only
    
    img.w = w;
    img.h = h;
    img.c = c;
    img.data = (unsigned char*)calloc(w * h * c, sizeof(unsigned char));
    return img;
}

void sod_free_image(sod_img img) {
    if (img.data) {
        free(img.data);
    }
}

sod_img sod_copy_image(sod_img img) {
    sod_img copy = sod_make_image(img.w, img.h, img.c);
    if (copy.data && img.data) {
        memcpy(copy.data, img.data, img.w * img.h * img.c * sizeof(unsigned char));
    }
    return copy;
}

float sod_img_get_pixel(sod_img img, int x, int y, int c) {
    __CPROVER_assume(x >= 0 && x < 4);  // Bound x
    __CPROVER_assume(y >= 0 && y < 4);  // Bound y
    __CPROVER_assume(c >= 0 && c < 3);  // Bound channels
    
    if (!img.data || x >= img.w || y >= img.h || c >= img.c) {
        return 0;
    }
    return img.data[(y * img.w + x) * img.c + c] / 255.0f;
}

void sod_img_set_pixel(sod_img img, int x, int y, int c, float val) {
    if (!img.data || x < 0 || x >= img.w || y < 0 || y >= img.h || c < 0 || c >= img.c) {
        return;
    }
    // Clamp value between 0 and 1
    if (val < 0) val = 0;
    if (val > 1) val = 1;
    img.data[(y * img.w + x) * img.c + c] = (unsigned char)(val * 255);
}

// Simplified stubs for file operations
sod_img sod_img_load_from_file(const char* path, int type) {
    // Return empty image for testing
    return sod_make_image(3, 3, 3);
}

int sod_img_save_as_jpeg(sod_img img, const char* path, int quality) {
    return SOD_OK;
}