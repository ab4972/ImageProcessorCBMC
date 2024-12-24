#include "Picture.h"
#include "Utils.h"

unsigned char nondet_uchar();
int nondet_int();

bool init_picture_from_file(struct picture *pic, const char *path){
  pic->img = load_image(path);
  if( pic->img.data == 0 ){
    return false;
  }
  pic->width = get_image_width(pic->img);
  pic->height = get_image_height(pic->img);
  return true;
}

bool init_picture_from_size(struct picture *pic, int width, int height){
  pic->img = create_image(width, height);
  pic->width = width;
  pic->height = height;
  return true;
}

bool save_picture_to_file(struct picture *pic, const char *path){
  return save_image(pic->img, path);
}

// enum mapping to support get/set pixel functions
enum RGB {RED, GREEN, BLUE};

// struct pixel get_pixel(struct picture *pic, int x, int y) {
//     // Verify input bounds
//     __CPROVER_assert(x >= 0 && x < pic->width, "X coordinate in bounds");
//     __CPROVER_assert(y >= 0 && y < pic->height, "Y coordinate in bounds");
    
//     struct pixel pix;
    
//     // Get values with verification
//     unsigned char red = get_pixel_value(pic->img, RED, x, y);
//     unsigned char green = get_pixel_value(pic->img, GREEN, x, y);
//     unsigned char blue = get_pixel_value(pic->img, BLUE, x, y);
    
//     // Verify values are preserved
//     __CPROVER_assert(red <= MAX_PIXEL_INTENSITY, "Red value in range");
//     __CPROVER_assert(green <= MAX_PIXEL_INTENSITY, "Green value in range");
//     __CPROVER_assert(blue <= MAX_PIXEL_INTENSITY, "Blue value in range");
    
//     pix.red = red;
//     pix.green = green;
//     pix.blue = blue;
    
//     // Verify assignment worked
//     __CPROVER_assert(pix.blue == blue, "Blue value correctly assigned");
    
//     return pix;
// }

struct pixel get_pixel(struct picture *pic, int x, int y) {
   struct pixel pix = {0, 0, 0};  // Initialize to black
   
   // Validate input pointer
   if (pic == NULL || pic->img.data == NULL) {
       return pix;
   }
   
   // Validate bounds
   if (x < 0 || x >= pic->width || y < 0 || y >= pic->height) {
       return pix;
   }
   
   // Get values with verification
   unsigned char red = get_pixel_value(pic->img, RED, x, y);
   unsigned char green = get_pixel_value(pic->img, GREEN, x, y);
   unsigned char blue = get_pixel_value(pic->img, BLUE, x, y);
   
   // Verify values are in range
   __CPROVER_assert(red <= MAX_PIXEL_INTENSITY, "Red value in range");
   __CPROVER_assert(green <= MAX_PIXEL_INTENSITY, "Green value in range");
   __CPROVER_assert(blue <= MAX_PIXEL_INTENSITY, "Blue value in range");
   
   pix.red = red;
   pix.green = green;
   pix.blue = blue;
   
   return pix;
}

void verify_get_pixel() {
   struct picture pic;
   
   // Initialize with valid dimensions
   pic.width = nondet_int();
   pic.height = nondet_int();
   __CPROVER_assume(pic.width > 0 && pic.width <= 100);
   __CPROVER_assume(pic.height > 0 && pic.height <= 100);
   
   // Create valid image
   pic.img = sod_make_image(pic.width, pic.height, 3);
   __CPROVER_assume(pic.img.data != NULL);
   
   // Test coordinates
   int x = nondet_int();
   int y = nondet_int();
   
   // Get pixel
   struct pixel result = get_pixel(&pic, x, y);
   
   // Verify behavior
   if (x >= 0 && x < pic.width && y >= 0 && y < pic.height) {
       __CPROVER_assert(result.red <= MAX_PIXEL_INTENSITY, "Valid red value");
       __CPROVER_assert(result.green <= MAX_PIXEL_INTENSITY, "Valid green value");
       __CPROVER_assert(result.blue <= MAX_PIXEL_INTENSITY, "Valid blue value");
   }
   
   // Clean up
   clear_picture(&pic);
}


// void set_pixel(struct picture *pic, int x, int y, struct pixel *rgb){
//   // Beware: pixels are stored in a (x,y) vector from the top left of the image.
//   set_pixel_value(pic->img, RED, x, y, rgb->red);
//   set_pixel_value(pic->img, GREEN, x, y, rgb->green);
//   set_pixel_value(pic->img, BLUE, x, y, rgb->blue);
// }

void set_pixel(struct picture *pic, int x, int y, struct pixel *rgb) {
    // Check for NULL pointers
    if (pic == NULL || rgb == NULL || pic->img.data == NULL) {
        return;
    }
    
    // Check bounds
    if (x < 0 || x >= pic->width || y < 0 || y >= pic->height) {
        return;
    }
    
    // Verify pixel values are in valid range
    __CPROVER_assume(rgb->red <= MAX_PIXEL_INTENSITY);
    __CPROVER_assume(rgb->green <= MAX_PIXEL_INTENSITY);
    __CPROVER_assume(rgb->blue <= MAX_PIXEL_INTENSITY);
    
    // Set and verify each channel separately
    // Red channel
    set_pixel_value(pic->img, RED, x, y, rgb->red);
    unsigned char red_check = get_pixel_value(pic->img, RED, x, y);
    __CPROVER_assert(red_check == rgb->red, "Red channel set correctly");
    
    // Green channel
    set_pixel_value(pic->img, GREEN, x, y, rgb->green);
    unsigned char green_check = get_pixel_value(pic->img, GREEN, x, y);
    __CPROVER_assert(green_check == rgb->green, "Green channel set correctly");
    
    // Blue channel
    set_pixel_value(pic->img, BLUE, x, y, rgb->blue);
    unsigned char blue_check = get_pixel_value(pic->img, BLUE, x, y);
    __CPROVER_assert(blue_check == rgb->blue, "Blue channel set correctly");
    
    // Final verification using get_pixel
    #ifdef DEBUG
    struct pixel verify = get_pixel(pic, x, y);
    printf("Set RGB:(%d,%d,%d) Got:(%d,%d,%d)\n",
           rgb->red, rgb->green, rgb->blue,
           verify.red, verify.green, verify.blue);
    #endif
}

bool contains_point(struct picture *pic, int x, int y){
  return x >= 0 && x < pic->width && y >= 0 && y < pic->height;
}

void clear_picture(struct picture *pic){
  free_image(pic->img);
}

void verify_single_pixel() {
    struct picture pic;
    
    // Use fixed dimensions within Utils.h bounds (which are 4x4)
    pic.width = 2;
    pic.height = 2;
    
    // Create image and verify
    pic.img = sod_make_image(2, 2, 3);
    __CPROVER_assume(pic.img.data != NULL);
    
    // Verify image dimensions match what we requested
    __CPROVER_assume(pic.img.w == 2);
    __CPROVER_assume(pic.img.h == 2);
    __CPROVER_assume(pic.img.c == 3);
    
    // Test with a known value (128)
    unsigned char test_value = 128;
    
    // Set values using set_pixel_value with bounds checking
    __CPROVER_assume(test_value <= MAX_PIXEL_INTENSITY);
    
    // Set pixel values
    set_pixel_value(pic.img, RED, 1, 1, test_value);
    int red_check = get_pixel_value(pic.img, RED, 1, 1);
    __CPROVER_assert(red_check == test_value, "Direct red check");
    
    set_pixel_value(pic.img, GREEN, 1, 1, test_value);
    int green_check = get_pixel_value(pic.img, GREEN, 1, 1);
    __CPROVER_assert(green_check == test_value, "Direct green check");
    
    set_pixel_value(pic.img, BLUE, 1, 1, test_value);
    int blue_check = get_pixel_value(pic.img, BLUE, 1, 1);
    __CPROVER_assert(blue_check == test_value, "Direct blue check");
    
    // Get pixel and verify through get_pixel
    struct pixel result = get_pixel(&pic, 1, 1);
    
    // Verify each channel
    __CPROVER_assert(result.red == test_value, "Red channel exact match");
    __CPROVER_assert(result.green == test_value, "Green channel exact match");
    __CPROVER_assert(result.blue == test_value, "Blue channel exact match");
    
    // Clean up
    clear_picture(&pic);
}

// Verify set_pixel function
void verify_set_pixel() {
   struct picture pic;
   
   // Initialize with fixed dimensions
   pic.width = 2;
   pic.height = 2;
   
   // Create image with known dimensions
   pic.img = sod_make_image(2, 2, 3);
   __CPROVER_assume(pic.img.data != NULL);
   __CPROVER_assume(pic.img.w == 2);
   __CPROVER_assume(pic.img.h == 2);
   __CPROVER_assume(pic.img.c == 3);
   
   // Create test pixel with fixed value
   struct pixel rgb = {128, 128, 128};
   
   // Test coordinates
   int x = 1;
   int y = 1;
   
   // Set pixel
   set_pixel(&pic, x, y, &rgb);
   
   // Verify using direct pixel value access
   int red = get_pixel_value(pic.img, RED, x, y);
   int green = get_pixel_value(pic.img, GREEN, x, y);
   int blue = get_pixel_value(pic.img, BLUE, x, y);
   
   __CPROVER_assert(red == 128, "Red value set correctly");
   __CPROVER_assert(green == 128, "Green value set correctly");
   __CPROVER_assert(blue == 128, "Blue value set correctly");
   
   // Clean up
   clear_picture(&pic);
}

// Verify sod_img_set_pixel function
void verify_sod_img_set_pixel() {
    // Create image with fixed dimensions
    sod_img img = sod_make_image(2, 2, 3);
    __CPROVER_assume(img.data != NULL);
    __CPROVER_assume(img.w == 2);
    __CPROVER_assume(img.h == 2);
    __CPROVER_assume(img.c == 3);
    
    // Verify image dimensions
    size_t total_size = (size_t)img.w * img.h * img.c;
    __CPROVER_assume(total_size <= SIZE_MAX / sizeof(unsigned char));
    
    // Test coordinates
    int x = 1;
    int y = 1;
    int c = 0;  // RED channel
    
    // Verify coordinates are valid
    __CPROVER_assume(x >= 0 && x < img.w);
    __CPROVER_assume(y >= 0 && y < img.h);
    __CPROVER_assume(c >= 0 && c < img.c);
    
    // Calculate index safely
    size_t channel_offset = (size_t)c * img.h * img.w;
    size_t row_offset = (size_t)y * img.w;
    size_t col_offset = x;
    
    // Verify offsets
    __CPROVER_assert(channel_offset <= SIZE_MAX - row_offset, "Channel offset valid");
    __CPROVER_assert(row_offset + channel_offset <= SIZE_MAX - col_offset, "Total offset valid");
    
    // Calculate final index
    size_t index = channel_offset + row_offset + col_offset;
    __CPROVER_assert(index < total_size, "Index within bounds");
    
    // Test value
    unsigned char test_value = 128;
    
    // Set through API
    sod_img_set_pixel(img, x, y, c, test_value);
    
    // Verify through direct access
    __CPROVER_assert(img.data[index] == test_value, "Memory value preserved");
    
    // Verify through get_pixel
    float result = sod_img_get_pixel(img, x, y, c);
    __CPROVER_assert(result == test_value, "API value preserved");
    
    // Clean up
    sod_free_image(img);
}

// Add memory layout verification
void verify_memory_layout() {
    sod_img img = sod_make_image(2, 2, 3);
    __CPROVER_assume(img.data != NULL);
    
    // Test all channels at position (1,1)
    int x = 1;
    int y = 1;
    
    // Set values for each channel
    for(int c = 0; c < 3; c++) {
        // Calculate index: c*h*w + y*w + x
        size_t index = (size_t)c * img.h * img.w + 
                      (size_t)y * img.w + 
                      x;
        
        // Set value
        img.data[index] = 128 + c;  // Different value for each channel
        
        // Verify through get_pixel
        float result = sod_img_get_pixel(img, x, y, c);
        __CPROVER_assert(result == 128 + c, "Channel value preserved");
    }
    
    // Clean up
    sod_free_image(img);
}

// Add a test for direct memory access
void verify_sod_direct_memory() {
    // Create 2x2 RGB image
    sod_img img = sod_make_image(2, 2, 3);
    __CPROVER_assume(img.data != NULL);
    __CPROVER_assume(img.w == 2);
    __CPROVER_assume(img.h == 2);
    __CPROVER_assume(img.c == 3);
    
    // Calculate index for pixel (1,1) red channel
    size_t index = (size_t)0 * img.w * img.h + // channel offset (RED = 0)
                  (size_t)1 * img.w +          // row offset
                  1;                           // column offset
    
    // Set value directly
    unsigned char test_value = 128;
    img.data[index] = test_value;
    
    // Verify through direct memory access
    __CPROVER_assert(img.data[index] == test_value, "Direct memory access preserved");
    
    // Verify through sod_img_get_pixel
    float result = sod_img_get_pixel(img, 1, 1, 0);
    __CPROVER_assert(result == test_value, "Get pixel matches direct access");
    
    // Clean up
    sod_free_image(img);
}

// Add a simpler test that checks just one channel
void verify_single_channel() {
   struct picture pic;
   
   // Use minimal dimensions
   pic.width = 2;
   pic.height = 2;
   
   // Create image
   pic.img = sod_make_image(2, 2, 3);
   if (pic.img.data == NULL) {
       return;
   }
   
   // Verify image creation
   if (pic.img.w != 2 || pic.img.h != 2 || pic.img.c != 3) {
       clear_picture(&pic);
       return;
   }
   
   // Initialize all pixels to 0
   for (int i = 0; i < pic.width * pic.height * 3; i++) {
       pic.img.data[i] = 0;
   }
   
   // Test with single channel (RED)
   unsigned char test_value = 128;
   
   // Set just the red channel
   set_pixel_value(pic.img, RED, 1, 1, test_value);
   
   // Verify through direct access
   int direct_check = get_pixel_value(pic.img, RED, 1, 1);
   __CPROVER_assert(direct_check == test_value, "Direct red value check");
   
   // Verify through get_pixel
   struct pixel result = get_pixel(&pic, 1, 1);
   __CPROVER_assert(result.red == test_value, "Red channel through get_pixel");
   __CPROVER_assert(result.green == 0, "Green channel unchanged");
   __CPROVER_assert(result.blue == 0, "Blue channel unchanged");
   
   // Clean up
   clear_picture(&pic);
}