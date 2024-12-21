#include "PicProcess.h"
#include "Picture.h"
#include "Utils.h"

#define NO_RGB_COMPONENTS 3
#define BLUR_REGION_SIZE 9

void invert_picture(struct picture *pic) {
  for (int i = 0; i < pic->width; i++) {
    for (int j = 0; j < pic->height; j++) {
      struct pixel rgb = get_pixel(pic, i, j);
      rgb.red = MAX_PIXEL_INTENSITY - rgb.red;
      rgb.green = MAX_PIXEL_INTENSITY - rgb.green;
      rgb.blue = MAX_PIXEL_INTENSITY - rgb.blue;
      set_pixel(pic, i, j, &rgb);
    }
  }
}

void grayscale_picture(struct picture *pic) {
  for (int i = 0; i < pic->width; i++) {
    for (int j = 0; j < pic->height; j++) {
      struct pixel rgb = get_pixel(pic, i, j);
      int avg = (rgb.red + rgb.green + rgb.blue) / NO_RGB_COMPONENTS;
      rgb.red = avg;
      rgb.green = avg;
      rgb.blue = avg;
      set_pixel(pic, i, j, &rgb);
    }
  }
}

void rotate_picture(struct picture *pic, int angle) {
  struct picture tmp;
  tmp.img = copy_image(pic->img);
  tmp.width = pic->width;
  tmp.height = pic->height;

  int new_width = tmp.width;
  int new_height = tmp.height;

  if (angle == 90 || angle == 270) {
    new_width = tmp.height;
    new_height = tmp.width;
  }

  clear_picture(pic);
  init_picture_from_size(pic, new_width, new_height);

  for (int i = 0; i < new_width; i++) {
    for (int j = 0; j < new_height; j++) {
      struct pixel rgb;
      switch (angle) {
        case (90):rgb = get_pixel(&tmp, j, new_width - 1 - i);
          break;
        case (180):rgb = get_pixel(&tmp, new_width - 1 - i, new_height - 1 - j);
          break;
        case (270):rgb = get_pixel(&tmp, new_height - 1 - j, i);
          break;
        default:printf("[!] rotate is undefined for angle %i (must be 90, 180 or 270)\n", angle);
          clear_picture(&tmp);
          return;
      }
      set_pixel(pic, i, j, &rgb);
    }
  }
  clear_picture(&tmp);
}

void flip_picture(struct picture *pic, char plane) {
  struct picture tmp;
  tmp.img = copy_image(pic->img);
  tmp.width = pic->width;
  tmp.height = pic->height;

  if (plane == 'V') {
    printf("flipping over V plane\n");
    for (int i = 0; i < tmp.width; i++) {
      for (int j = 0; j < tmp.height; j++) {
        struct pixel rgb = get_pixel(&tmp, i, tmp.height - 1 - j);
        set_pixel(pic, i, j, &rgb);
      }
    }
  } else if (plane == 'H') {
    printf("flipping over H plane\n");
    for (int i = 0; i < tmp.width; i++) {
      for (int j = 0; j < tmp.height; j++) {
        struct pixel rgb = get_pixel(&tmp, tmp.width - 1 - i, j);
        set_pixel(pic, i, j, &rgb);
      }
    }
  } else {
    printf("[!] flip is undefined for plane %c\n", plane);
  }
  clear_picture(&tmp);
}

void blur_picture(struct picture *pic) {
  struct picture tmp;
  tmp.img = copy_image(pic->img);
  tmp.width = pic->width;
  tmp.height = pic->height;

  for (int i = 1; i < tmp.width - 1; i++) {
    for (int j = 1; j < tmp.height - 1; j++) {

      struct pixel rgb;
      int sum_red = 0;
      int sum_green = 0;
      int sum_blue = 0;

      for (int n = -1; n <= 1; n++) {
        for (int m = -1; m <= 1; m++) {
          rgb = get_pixel(&tmp, i + n, j + m);
          sum_red += rgb.red;
          sum_green += rgb.green;
          sum_blue += rgb.blue;
        }
      }

      rgb.red = sum_red / BLUR_REGION_SIZE;
      rgb.green = sum_green / BLUR_REGION_SIZE;
      rgb.blue = sum_blue / BLUR_REGION_SIZE;

      set_pixel(pic, i, j, &rgb);
    }
  }
  clear_picture(&tmp);
}

// // CBMC verification harness
// void __CPROVER_assert(int condition, const char* message);
// void __CPROVER_assume(int condition);
unsigned char nondet_uchar();
int nondet_int();

void verify_grayscale() {
    struct picture pic;
    pic.width = nondet_int();
    pic.height = nondet_int();
    
    // Constrain size to small values for faster verification
    __CPROVER_assume(pic.width > 0 && pic.width <= 3);
    __CPROVER_assume(pic.height > 0 && pic.height <= 3);
    
    // Create SOD image
    pic.img = sod_make_image(pic.width, pic.height, NO_RGB_COMPONENTS);
    __CPROVER_assume(pic.img.data != NULL);
    
    // Initialize pixels with nondeterministic values
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel rgb;
            rgb.red = nondet_int();
            rgb.green = nondet_int();
            rgb.blue = nondet_int();
            // Ensure input values are within valid range
            __CPROVER_assume(rgb.red <= MAX_PIXEL_INTENSITY);
            __CPROVER_assume(rgb.green <= MAX_PIXEL_INTENSITY);
            __CPROVER_assume(rgb.blue <= MAX_PIXEL_INTENSITY);
            __CPROVER_assume(rgb.red >= 0);
            __CPROVER_assume(rgb.green >= 0);
            __CPROVER_assume(rgb.blue >= 0);
            set_pixel(&pic, i, j, &rgb);
        }
    }
    
    // Store original values for verification
    struct picture original;
    original.width = pic.width;
    original.height = pic.height;
    original.img = sod_make_image(pic.width, pic.height, NO_RGB_COMPONENTS);
    __CPROVER_assume(original.img.data != NULL);
    
    // Copy original values
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel rgb = get_pixel(&pic, i, j);
            set_pixel(&original, i, j, &rgb);
        }
    }
    
    // Run grayscale conversion
    grayscale_picture(&pic);
    
    // Verify properties
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel p = get_pixel(&pic, i, j);
            // Add constraints on returned values
            __CPROVER_assume(p.red >= 0 && p.red <= 255);
            __CPROVER_assume(p.green >= 0 && p.green <= 255);
            __CPROVER_assume(p.blue >= 0 && p.blue <= 255);
            struct pixel orig = get_pixel(&original, i, j);
            // look at get_pixel function 
            __CPROVER_assume(orig.red >= 0 && orig.red <= 255);
            __CPROVER_assume(orig.green >= 0 && orig.green <= 255);
            __CPROVER_assume(orig.blue >= 0 && orig.blue <= 255);
            
            // Property 1: All RGB values should be equal
            __CPROVER_assert(p.red == p.green && p.green == p.blue,
                "RGB values must be equal in grayscale");
            
            // Property 2: Values should not exceed MAX_PIXEL_INTENSITY
            __CPROVER_assert(p.red <= MAX_PIXEL_INTENSITY,
                "Pixel values must not exceed maximum intensity");
            
            // Property 3: Average calculation is correct
            // Use unsigned int for sum to prevent overflow
            unsigned int sum = (unsigned int)orig.red + 
                             (unsigned int)orig.green + 
                             (unsigned int)orig.blue;
            unsigned char expected_avg = (unsigned char)(sum / NO_RGB_COMPONENTS);
            
            __CPROVER_assert(p.red == expected_avg,
                "Grayscale value must be average of original RGB values");
        }
    }
    
    // Clean up
    clear_picture(&pic);
    clear_picture(&original);
}

void verify_invert() {
    // Create a small bounded picture for faster verification
    struct picture pic;
    pic.width = nondet_int();
    pic.height = nondet_int();
    
    // Constrain size to small values for faster verification
    __CPROVER_assume(pic.width > 0 && pic.width <= 2);
    __CPROVER_assume(pic.height > 0 && pic.height <= 2);
    
    // Create SOD image
    pic.img = sod_make_image(pic.width, pic.height, NO_RGB_COMPONENTS);
    __CPROVER_assume(pic.img.data != NULL);  // Check the data pointer instead of img itself
    
    // Initialize pixels with nondeterministic values
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel rgb;
            rgb.red = nondet_uchar();
            rgb.green = nondet_uchar();
            rgb.blue = nondet_uchar();
            __CPROVER_assume(rgb.red <= MAX_PIXEL_INTENSITY);
            __CPROVER_assume(rgb.green <= MAX_PIXEL_INTENSITY);
            __CPROVER_assume(rgb.blue <= MAX_PIXEL_INTENSITY);
            set_pixel(&pic, i, j, &rgb);
        }
    }
    
    // Store original values for verification
    struct picture original;
    original.width = pic.width;
    original.height = pic.height;
    original.img = sod_make_image(pic.width, pic.height, NO_RGB_COMPONENTS);
    __CPROVER_assume(original.img.data != NULL);  // Check the data pointer instead of img itself
    
    // Copy original values
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel rgb = get_pixel(&pic, i, j);
            set_pixel(&original, i, j, &rgb);
        }
    }
    
    // Run invert operation
    invert_picture(&pic);
    
    // Verify properties
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel p = get_pixel(&pic, i, j);
            struct pixel orig = get_pixel(&original, i, j);  // Use get_pixel instead of array access
            
            // Property 1: Each color channel should be inverted correctly
            __CPROVER_assert(p.red == MAX_PIXEL_INTENSITY - orig.red,
                "Red channel should be correctly inverted");
            __CPROVER_assert(p.green == MAX_PIXEL_INTENSITY - orig.green,
                "Green channel should be correctly inverted");
            __CPROVER_assert(p.blue == MAX_PIXEL_INTENSITY - orig.blue,
                "Blue channel should be correctly inverted");
            
            // Property 2: Values should not exceed MAX_PIXEL_INTENSITY
            __CPROVER_assert(p.red <= MAX_PIXEL_INTENSITY,
                "Red value must not exceed maximum intensity");
            __CPROVER_assert(p.green <= MAX_PIXEL_INTENSITY,
                "Green value must not exceed maximum intensity");
            __CPROVER_assert(p.blue <= MAX_PIXEL_INTENSITY,
                "Blue value must not exceed maximum intensity");
            
            // Property 3: Double inversion should return original values
            struct pixel double_invert = p;
            double_invert.red = MAX_PIXEL_INTENSITY - p.red;
            double_invert.green = MAX_PIXEL_INTENSITY - p.green;
            double_invert.blue = MAX_PIXEL_INTENSITY - p.blue;
            
            __CPROVER_assert(double_invert.red == orig.red,
                "Double inversion should return original red value");
            __CPROVER_assert(double_invert.green == orig.green,
                "Double inversion should return original green value");
            __CPROVER_assert(double_invert.blue == orig.blue,
                "Double inversion should return original blue value");
        }
    }
    
    // Clean up
    clear_picture(&pic);
    clear_picture(&original);
}

void verify_rotate_picture() {
    // Create a small bounded picture for faster verification
    struct picture pic;
    pic.width = nondet_int();
    pic.height = nondet_int();
    
    // Constrain size to small values for faster verification
    __CPROVER_assume(pic.width > 0 && pic.width <= 2);
    __CPROVER_assume(pic.height > 0 && pic.height <= 2);
    
    // Create SOD image
    pic.img = sod_make_image(pic.width, pic.height, NO_RGB_COMPONENTS);
    __CPROVER_assume(pic.img.data != NULL);
    
    // Initialize pixels with nondeterministic values
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel rgb;
            rgb.red = nondet_uchar();
            rgb.green = nondet_uchar();
            rgb.blue = nondet_uchar();
            __CPROVER_assume(rgb.red <= MAX_PIXEL_INTENSITY);
            __CPROVER_assume(rgb.green <= MAX_PIXEL_INTENSITY);
            __CPROVER_assume(rgb.blue <= MAX_PIXEL_INTENSITY);
            set_pixel(&pic, i, j, &rgb);
        }
    }
    
    // Store original values for verification
    struct picture original;
    original.width = pic.width;
    original.height = pic.height;
    original.img = sod_make_image(pic.width, pic.height, NO_RGB_COMPONENTS);
    __CPROVER_assume(original.img.data != NULL);
    
    // Copy original values
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel rgb = get_pixel(&pic, i, j);
            set_pixel(&original, i, j, &rgb);
        }
    }
    
    // Test 90-degree rotation
    rotate_picture(&pic, 90);
    
    // Verify 90-degree rotation properties
    __CPROVER_assert(pic.width == original.height, 
        "90-degree rotation should swap width and height");
    __CPROVER_assert(pic.height == original.width,
        "90-degree rotation should swap width and height");
        
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel rotated = get_pixel(&pic, i, j);
            struct pixel orig = get_pixel(&original, j, pic.width - 1 - i);
            
            __CPROVER_assert(rotated.red == orig.red &&
                            rotated.green == orig.green &&
                            rotated.blue == orig.blue,
                "90-degree rotation should preserve pixel values");
        }
    }
    
    // Test that four 90-degree rotations return to original
    rotate_picture(&pic, 90);
    rotate_picture(&pic, 90);
    rotate_picture(&pic, 90);
    
    // Verify return to original state
    __CPROVER_assert(pic.width == original.width,
        "Four 90-degree rotations should restore original dimensions");
    __CPROVER_assert(pic.height == original.height,
        "Four 90-degree rotations should restore original dimensions");
        
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel final = get_pixel(&pic, i, j);
            struct pixel orig = get_pixel(&original, i, j);
            
            __CPROVER_assert(final.red == orig.red &&
                            final.green == orig.green &&
                            final.blue == orig.blue,
                "Four 90-degree rotations should return to original state");
        }
    }
    
    // Test 180-degree rotation
    rotate_picture(&pic, 180);
    
    // Verify 180-degree rotation properties
    __CPROVER_assert(pic.width == original.width,
        "180-degree rotation should preserve dimensions");
    __CPROVER_assert(pic.height == original.height,
        "180-degree rotation should preserve dimensions");
        
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel rotated = get_pixel(&pic, i, j);
            struct pixel orig = get_pixel(&original, pic.width - 1 - i, pic.height - 1 - j);
            
            __CPROVER_assert(rotated.red == orig.red &&
                            rotated.green == orig.green &&
                            rotated.blue == orig.blue,
                "180-degree rotation should preserve pixel values");
        }
    }
    
    // Clean up
    clear_picture(&pic);
    clear_picture(&original);
}

void verify_flip_picture() {
    // Create a small bounded picture for faster verification
    struct picture pic;
    pic.width = nondet_int();
    pic.height = nondet_int();
    
    // Constrain size to small values for faster verification
    __CPROVER_assume(pic.width > 0 && pic.width <= 2);
    __CPROVER_assume(pic.height > 0 && pic.height <= 2);
    
    // Create SOD image
    pic.img = sod_make_image(pic.width, pic.height, NO_RGB_COMPONENTS);
    __CPROVER_assume(pic.img.data != NULL);
    
    // Initialize pixels with nondeterministic values
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel rgb;
            rgb.red = nondet_uchar();
            rgb.green = nondet_uchar();
            rgb.blue = nondet_uchar();
            __CPROVER_assume(rgb.red <= MAX_PIXEL_INTENSITY);
            __CPROVER_assume(rgb.green <= MAX_PIXEL_INTENSITY);
            __CPROVER_assume(rgb.blue <= MAX_PIXEL_INTENSITY);
            set_pixel(&pic, i, j, &rgb);
        }
    }
    
    // Store original values for verification
    struct picture original;
    original.width = pic.width;
    original.height = pic.height;
    original.img = sod_make_image(pic.width, pic.height, NO_RGB_COMPONENTS);
    __CPROVER_assume(original.img.data != NULL);
    
    // Copy original values
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel rgb = get_pixel(&pic, i, j);
            set_pixel(&original, i, j, &rgb);
        }
    }
    
    // Test vertical flip
    flip_picture(&pic, 'V');
    
    // Verify vertical flip properties
    __CPROVER_assert(pic.width == original.width,
        "Vertical flip should preserve width");
    __CPROVER_assert(pic.height == original.height,
        "Vertical flip should preserve height");
        
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel flipped = get_pixel(&pic, i, j);
            struct pixel orig = get_pixel(&original, i, pic.height - 1 - j);
            
            __CPROVER_assert(flipped.red == orig.red &&
                            flipped.green == orig.green &&
                            flipped.blue == orig.blue,
                "Vertical flip should preserve pixel values");
        }
    }
    
    // Test that double vertical flip returns to original
    flip_picture(&pic, 'V');
    
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel final = get_pixel(&pic, i, j);
            struct pixel orig = get_pixel(&original, i, j);
            
            __CPROVER_assert(final.red == orig.red &&
                            final.green == orig.green &&
                            final.blue == orig.blue,
                "Double vertical flip should return to original state");
        }
    }
    
    // Test horizontal flip
    flip_picture(&pic, 'H');
    
    // Verify horizontal flip properties
    __CPROVER_assert(pic.width == original.width,
        "Horizontal flip should preserve width");
    __CPROVER_assert(pic.height == original.height,
        "Horizontal flip should preserve height");
        
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel flipped = get_pixel(&pic, i, j);
            struct pixel orig = get_pixel(&original, pic.width - 1 - i, j);
            
            __CPROVER_assert(flipped.red == orig.red &&
                            flipped.green == orig.green &&
                            flipped.blue == orig.blue,
                "Horizontal flip should preserve pixel values");
        }
    }
    
    // Test that double horizontal flip returns to original
    flip_picture(&pic, 'H');
    
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel final = get_pixel(&pic, i, j);
            struct pixel orig = get_pixel(&original, i, j);
            
            __CPROVER_assert(final.red == orig.red &&
                            final.green == orig.green &&
                            final.blue == orig.blue,
                "Double horizontal flip should return to original state");
        }
    }
    
    // Test invalid flip plane
    flip_picture(&pic, 'X');
    
    // Verify image remains unchanged after invalid flip
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel final = get_pixel(&pic, i, j);
            struct pixel orig = get_pixel(&original, i, j);
            
            __CPROVER_assert(final.red == orig.red &&
                            final.green == orig.green &&
                            final.blue == orig.blue,
                "Invalid flip should not modify the image");
        }
    }
    
    // Clean up
    clear_picture(&pic);
    clear_picture(&original);
}

void verify_blur_picture() {
    // Create a small bounded picture for faster verification
    struct picture pic;
    pic.width = nondet_int();
    pic.height = nondet_int();
    
    // Constrain size to small values for faster verification
    // Need at least 3x3 for blur to work on inner pixels
    __CPROVER_assume(pic.width == 3);  // Fixed size for blur verification
    __CPROVER_assume(pic.height == 3);
    
    // Create SOD image
    pic.img = sod_make_image(pic.width, pic.height, NO_RGB_COMPONENTS);
    __CPROVER_assume(pic.img.data != NULL);
    
    // Initialize pixels with nondeterministic values
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel rgb;
            rgb.red = nondet_uchar();
            rgb.green = nondet_uchar();
            rgb.blue = nondet_uchar();
            __CPROVER_assume(rgb.red <= MAX_PIXEL_INTENSITY);
            __CPROVER_assume(rgb.green <= MAX_PIXEL_INTENSITY);
            __CPROVER_assume(rgb.blue <= MAX_PIXEL_INTENSITY);
            set_pixel(&pic, i, j, &rgb);
        }
    }
    
    // Store original values for verification
    struct picture original;
    original.width = pic.width;
    original.height = pic.height;
    original.img = sod_make_image(pic.width, pic.height, NO_RGB_COMPONENTS);
    __CPROVER_assume(original.img.data != NULL);
    
    // Copy original values
    for (int i = 0; i < pic.width; i++) {
        for (int j = 0; j < pic.height; j++) {
            struct pixel rgb = get_pixel(&pic, i, j);
            set_pixel(&original, i, j, &rgb);
        }
    }
    
    // Run blur operation
    blur_picture(&pic);
    
    // Verify properties
    // We only check the center pixel (1,1) as it's the only one fully surrounded
    // by neighbors in a 3x3 image
    struct pixel blurred = get_pixel(&pic, 1, 1);
    
    // Calculate expected blur values for center pixel
    int expected_red = 0;
    int expected_green = 0;
    int expected_blue = 0;
    
    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 3; j++) {
            struct pixel orig = get_pixel(&original, i, j);
            expected_red += orig.red;
            expected_green += orig.green;
            expected_blue += orig.blue;
        }
    }
    
    expected_red /= BLUR_REGION_SIZE;
    expected_green /= BLUR_REGION_SIZE;
    expected_blue /= BLUR_REGION_SIZE;
    
    // Verify blur calculations
    __CPROVER_assert(blurred.red == expected_red,
        "Center pixel red value should be average of 3x3 neighborhood");
    __CPROVER_assert(blurred.green == expected_green,
        "Center pixel green value should be average of 3x3 neighborhood");
    __CPROVER_assert(blurred.blue == expected_blue,
        "Center pixel blue value should be average of 3x3 neighborhood");
    
    // Verify values don't exceed maximum intensity
    __CPROVER_assert(blurred.red <= MAX_PIXEL_INTENSITY,
        "Blurred red value must not exceed maximum intensity");
    __CPROVER_assert(blurred.green <= MAX_PIXEL_INTENSITY,
        "Blurred green value must not exceed maximum intensity");
    __CPROVER_assert(blurred.blue <= MAX_PIXEL_INTENSITY,
        "Blurred blue value must not exceed maximum intensity");
    
    // Verify edge pixels remain unchanged
    // Top edge
    for (int i = 0; i < pic.width; i++) {
        struct pixel edge = get_pixel(&pic, i, 0);
        struct pixel orig = get_pixel(&original, i, 0);
        __CPROVER_assert(edge.red == orig.red &&
                        edge.green == orig.green &&
                        edge.blue == orig.blue,
                        "Top edge pixels should remain unchanged");
    }
    
    // Bottom edge
    for (int i = 0; i < pic.width; i++) {
        struct pixel edge = get_pixel(&pic, i, pic.height - 1);
        struct pixel orig = get_pixel(&original, i, pic.height - 1);
        __CPROVER_assert(edge.red == orig.red &&
                        edge.green == orig.green &&
                        edge.blue == orig.blue,
                        "Bottom edge pixels should remain unchanged");
    }
    
    // Left edge
    for (int j = 0; j < pic.height; j++) {
        struct pixel edge = get_pixel(&pic, 0, j);
        struct pixel orig = get_pixel(&original, 0, j);
        __CPROVER_assert(edge.red == orig.red &&
                        edge.green == orig.green &&
                        edge.blue == orig.blue,
                        "Left edge pixels should remain unchanged");
    }
    
    // Right edge
    for (int j = 0; j < pic.height; j++) {
        struct pixel edge = get_pixel(&pic, pic.width - 1, j);
        struct pixel orig = get_pixel(&original, pic.width - 1, j);
        __CPROVER_assert(edge.red == orig.red &&
                        edge.green == orig.green &&
                        edge.blue == orig.blue,
                        "Right edge pixels should remain unchanged");
    }
    
    // Clean up
    clear_picture(&pic);
    clear_picture(&original);
}
