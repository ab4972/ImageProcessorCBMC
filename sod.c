#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "sod.h"

/* Create a new image */
sod_img sod_make_image(int w, int h, int c) {
    sod_img im = { 0 };
    im.h = h;
    im.w = w;
    im.c = c;
    im.data = (float*)calloc(h * w * c, sizeof(float));
    return im;
}

/* Free image memory */
void sod_free_image(sod_img m) {
    if (m.data) {
        free(m.data);
    }
}

/* Get pixel value */
float sod_img_get_pixel(sod_img m, int x, int y, int c) {
    if (x < 0 || x >= m.w || y < 0 || y >= m.h || c < 0 || c >= m.c) return 0;
    return m.data[c * m.h * m.w + y * m.w + x];
}

/* Set pixel value */
void sod_img_set_pixel(sod_img m, int x, int y, int c, float val) {
    if (x < 0 || x >= m.w || y < 0 || y >= m.h || c < 0 || c >= m.c) return;
    m.data[c * m.h * m.w + y * m.w + x] = val;
}