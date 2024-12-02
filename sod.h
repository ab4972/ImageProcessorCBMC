#ifndef _SOD_H_
#define _SOD_H_

#ifdef __cplusplus
extern "C" {
#endif

    /* Essential image structure */
    typedef struct sod_img {
        int h;   /* Image height */
        int w;   /* Image width */
        int c;   /* Number of channels (1 for grayscale, 3 for RGB) */
        float* data; /* Pixel data */
    } sod_img;

    /* Essential constants */
#define SOD_IMG_COLOR     0

/* Essential functions */
    sod_img sod_make_image(int w, int h, int c);
    void sod_free_image(sod_img m);
    float sod_img_get_pixel(sod_img m, int x, int y, int c);
    void sod_img_set_pixel(sod_img m, int x, int y, int c, float val);

    /* Return codes */
#define SOD_OK           0
#define SOD_OUTOFMEM    -4

#ifdef __cplusplus
}
#endif
#endif /* _SOD_H_ */