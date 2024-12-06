#include "Utils.h"
#include "simple_sod.h"
#ifdef _WIN32
    #include <io.h>
    #define access _access
    #define F_OK 0
#else
    #include <unistd.h>
#endif
#include <stdio.h>

#define DEFAULT_COMPRESSION_QUALITY -1
#define FULL_COLOUR_CHANNELS 3

sod_img create_image(int width, int height) {
  __CPROVER_assume(width >= 0 && width <= 4);
  __CPROVER_assume(height >= 0 && height <= 4);
  return sod_make_image(width, height, FULL_COLOUR_CHANNELS);
}

void free_image(sod_img img) {
  sod_free_image(img);
}

sod_img load_image(const char *path) {
    sod_img input = {0};
    
    // Allow CBMC to choose dimensions within bounds
    input.w = nondet_int();
    input.h = nondet_int();
    input.c = nondet_int();
    
    // But constrain them
    __CPROVER_assume(input.w > 0 && input.w <= 4);
    __CPROVER_assume(input.h > 0 && input.h <= 4);
    __CPROVER_assume(input.c > 0 && input.c <= 3);
    
    input.data = (unsigned char*)calloc(input.w * input.h * input.c, sizeof(unsigned char));
    
    // If allocation succeeds, initialize with non-deterministic values
    if (input.data) {
        for(int i = 0; i < input.w * input.h * input.c; i++) {
            input.data[i] = nondet_uchar();
            __CPROVER_assume(input.data[i] <= 255);
        }
    }
    
    return input;
}

bool save_image(sod_img img, const char *path) {
  int ret = sod_img_save_as_jpeg(img, path, DEFAULT_COMPRESSION_QUALITY);
  if (ret != SOD_OK) {
    printf("[!] error saving file to %s\n", path);
    return false;
  }
  return true;
}

sod_img copy_image(sod_img img) {
  sod_img copy = {0};
  __CPROVER_assume(img.w <= 4 && img.h <= 4);
  __CPROVER_assume(img.c <= 3);
  
  copy = sod_copy_image(img);
  return copy;
}

int get_image_width(sod_img img) {
  return img.w;
}

int get_image_height(sod_img img) {
  return img.h;
}

int get_pixel_value(sod_img img, int rgb, int x, int y) {
  __CPROVER_assume(x >= 0 && x < 4);
  __CPROVER_assume(y >= 0 && y < 4);
  __CPROVER_assume(rgb >= 0 && rgb < 3);
  
  float intensity = sod_img_get_pixel(img, x, y, rgb);
  int rgb_value = intensity * MAX_PIXEL_INTENSITY;
  return rgb_value;
}

void set_pixel_value(sod_img img, int rgb, int x, int y, int val) {
  __CPROVER_assume(x >= 0 && x < 4);
  __CPROVER_assume(y >= 0 && y < 4);
  __CPROVER_assume(rgb >= 0 && rgb < 3);
  __CPROVER_assume(val >= 0 && val <= 255);
  
  float intensity = val / MAX_PIXEL_INTENSITY;
  sod_img_set_pixel(img, x, y, rgb, intensity);
}
