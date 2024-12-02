#ifndef PICLIB_H
#define PICLIB_H

#include "Picture.h"
#include "Utils.h"

// picture transformation routines
void invert_picture(struct picture *pic);
void grayscale_picture(struct picture *pic);
void rotate_picture(struct picture *pic, int angle);
void flip_picture(struct picture *pic, char plane);
void blur_picture(struct picture *pic);
void verify_grayscale();
void verify_invert();
void verify_flip_picture();
void verify_rotate_picture();
void verify_blur_picture();
#endif

