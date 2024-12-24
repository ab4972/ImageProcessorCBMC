#ifndef SOD_H
#define SOD_H

#define SOD_OK 0
#define SOD_IMG_COLOR 0

// Simple image structure
typedef struct sod_img {
    unsigned char *data;  // Pixel data
    int w;               // Width
    int h;               // Height
    int c;               // Channels (3 for RGB)
} sod_img;

// Core functions used in your code

// void *memcpy(void *dst, const void *src, size_t n);
// void *__builtin___memcpy_chk(void *dst, const void *src, __CPROVER_size_t n, __CPROVER_size_t size);

sod_img sod_make_image(int w, int h, int c);
void sod_free_image(sod_img img);
sod_img sod_copy_image(sod_img img);

float sod_img_get_pixel(sod_img img, int x, int y, int c);
void sod_img_set_pixel(sod_img img, int x, int y, int c, float val);
sod_img sod_img_load_from_file(const char* path, int type);
int sod_img_save_as_jpeg(sod_img img, const char* path, int quality);


#endif