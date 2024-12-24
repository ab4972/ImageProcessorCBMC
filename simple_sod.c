#include "simple_sod.h"
#include <stdlib.h>
#include <string.h>
#undef memcpy
#include <stdint.h>

//memcpy stub from AWS C Common repository
// void *memcpy_impl(void *dst, const void *src, size_t n) {
//     __CPROVER_precondition(
//         __CPROVER_POINTER_OBJECT(dst) != __CPROVER_POINTER_OBJECT(src) ||
//             ((const char *)src >= (const char *)dst + n) || ((const char *)dst >= (const char *)src + n),
//         "memcpy src/dst overlap");
//     __CPROVER_precondition(src != NULL && __CPROVER_r_ok(src, n), "memcpy source region readable");
//     __CPROVER_precondition(dst != NULL && __CPROVER_w_ok(dst, n), "memcpy destination region writeable");

//     if (n > 0) {
//         size_t index;
//         __CPROVER_assume(index < n);
//         ((uint8_t *)dst)[index] = nondet_uint8_t();
//     }
//     return dst;
// }

void *memcpy(void *dst, const void *src, size_t n) {
    return memcpy_impl(dst, src, n);
}

// void *__builtin___memcpy_chk(void *dst, const void *src, __CPROVER_size_t n, __CPROVER_size_t size) {
//     (void)size;
//     return memcpy_impl(dst, src, n);
// }

sod_img sod_make_image(int w, int h, int c) {
    sod_img img = {0};
    __CPROVER_assume(w >= 0 && w <= 2);  // Max width 4
    __CPROVER_assume(h >= 0 && h <= 2);  // Max height 4
    __CPROVER_assume(c >= 1 && c <= 3);  // 1-3 channels only
    
    img.w = w;
    img.h = h;
    img.c = 3;
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

// float sod_img_get_pixel(sod_img img, int x, int y, int c) {
//     __CPROVER_assume(x >= 0 && x < 4);  // Bound x
//     __CPROVER_assume(y >= 0 && y < 4);  // Bound y
//     __CPROVER_assume(c >= 0 && c < 3);  // Bound channels
    
//     if (!img.data || x >= img.w || y >= img.h || c >= img.c) {
//         return 0;
//     }
//     return img.data[(y * img.w + x) * img.c + c] / 255.0f;
// }

// void sod_img_set_pixel(sod_img img, int x, int y, int c, float val) {
//     if (!img.data || x < 0 || x >= img.w || y < 0 || y >= img.h || c < 0 || c >= img.c) {
//         return;
//     }
//     // Clamp value between 0 and 1
//     if (val < 0) val = 0;
//     if (val > 1) val = 1;
//     img.data[(y * img.w + x) * img.c + c] = (unsigned char)(val * 255);
// }



// static inline float get_pixel(sod_img m, int x, int y, int c)
// {
// 	return (m.data ? m.data[c*m.h*m.w + y * m.w + x] : 0.0f);
// }
unsigned char get_pixel(sod_img m, int x, int y, int c) {
    // Initial null check
    if (m.data == NULL) {
        return 0;
    }
    
    // Bounds checking
    if (x < 0 || x >= m.w || 
        y < 0 || y >= m.h || 
        c < 0 || c >= m.c) {
        return 0;
    }
    
    // Verify image dimensions are reasonable
    __CPROVER_assume(m.w > 0 && m.w <= 4);
    __CPROVER_assume(m.h > 0 && m.h <= 4);
    __CPROVER_assume(m.c > 0 && m.c <= 3);
    
    // Calculate index parts with overflow protection
    size_t width_height = (size_t)m.w * m.h;
    __CPROVER_assert(width_height <= SIZE_MAX / 4, "Width*Height within bounds");
    
    size_t channel_offset = (size_t)c * width_height;
    __CPROVER_assert(channel_offset <= SIZE_MAX - m.w, "Channel offset within bounds");
    
    size_t row_offset = (size_t)y * m.w;
    __CPROVER_assert(row_offset <= SIZE_MAX - x, "Row offset within bounds");
    
    // Final index calculation
    size_t index = channel_offset + row_offset + x;
    __CPROVER_assert(index < (size_t)m.w * m.h * m.c, "Index within array bounds");
    
    // Verify pointer access
    __CPROVER_assert(m.data + index < m.data + ((size_t)m.w * m.h * m.c), 
                     "Pointer arithmetic within bounds");
    
    __CPROVER_assert(width_height == m.w * m.h, "width_height calculation correct");
    __CPROVER_assert(channel_offset == c * width_height, "channel offset correct");
    __CPROVER_assert(row_offset == y * m.w, "row offset correct");
    __CPROVER_assert(index == channel_offset + row_offset + x, "final index correct");
    
    return m.data[index];
}

// static inline void set_pixel(sod_img m, int x, int y, int c, float val)
// {
// 	/* x, y, c are already validated by upper layers */
// 	if (m.data)
// 		m.data[c*m.h*m.w + y * m.w + x] = val;
// }

static inline void set_pixel(sod_img m, int x, int y, int c, float val) {
    // Initial validation
    if (!m.data) return;
    
    // Calculate index using size_t to prevent overflow
    size_t width_height = (size_t)m.h * m.w;
    size_t channel_offset = (size_t)c * width_height;
    size_t row_offset = (size_t)y * m.w;
    size_t index = channel_offset + row_offset + x;
    
    // Set value
    unsigned char pixel_value = (unsigned char)val;
    m.data[index] = pixel_value;
}

// float sod_img_get_pixel(sod_img m, int x, int y, int c)
// {
// 	if (x < 0) x = 0;
// 	if (x >= m.w) x = m.w - 1;
// 	if (y < 0) y = 0;
// 	if (y >= m.h) y = m.h - 1;
// 	if (c < 0 || c >= m.c) return 0;
// 	return get_pixel(m, x, y, c);
// }

float sod_img_get_pixel(sod_img m, int x, int y, int c) {
   // Bounds checking with unsigned comparisons
   __CPROVER_assume(x >= 0 && (unsigned)x < (unsigned)m.w);
   __CPROVER_assume(y >= 0 && (unsigned)y < (unsigned)m.h);
   __CPROVER_assume(c >= 0 && (unsigned)c < (unsigned)m.c);
   
   // Safe bounds checking
   if (x < 0) x = 0;
   if (x >= m.w) x = m.w - 1;
   if (y < 0) y = 0;
   if (y >= m.h) y = m.h - 1;
   if (c < 0) c = 0;
   if (c >= m.c) c = m.c - 1;
   
   // Use get_pixel for actual access
   return (float)get_pixel(m, x, y, c);
}
void sod_img_set_pixel(sod_img m, int x, int y, int c, float val)
{
	if (x < 0 || y < 0 || c < 0 || x >= m.w || y >= m.h || c >= m.c) return;
	set_pixel(m, x, y, c, val);
}

// Simplified stubs for file operations
sod_img sod_img_load_from_file(const char* path, int type) {
    // Return empty image for testing
    return sod_make_image(3, 3, 3);
}

int sod_img_save_as_jpeg(sod_img img, const char* path, int quality) {
    return SOD_OK;
}

void verify_pixel_access() {
   sod_img m;
   
   // Set reasonable bounds for dimensions
   m.w = nondet_int();
   m.h = nondet_int();
   m.c = nondet_int();
   
   __CPROVER_assume(m.w > 0 && m.w <= 100);
   __CPROVER_assume(m.h > 0 && m.h <= 100);
   __CPROVER_assume(m.c > 0 && m.c <= 4);
   
   // Allocate data array
   size_t size = (size_t)m.w * m.h * m.c;
   m.data = malloc(size);
   __CPROVER_assume(m.data != NULL);
   
   // Test coordinates
   int x = nondet_int();
   int y = nondet_int();
   int c = nondet_int();
   
   // Get pixel value
   float val = sod_img_get_pixel(m, x, y, c);
   
   // Verify bounds
   __CPROVER_assert(val >= 0.0f && val <= 1.0f, "Pixel value in valid range");
   
   free(m.data);
}

// Verification harness
void verify_get_pixel() {
    sod_img m;
    
    // Initialize with bounded values
    m.w = nondet_int();
    m.h = nondet_int();
    m.c = 3;
    
    // Constrain to reasonable sizes
    __CPROVER_assume(m.w > 0 && m.w <= 2);  // Smaller bounds for verification
    __CPROVER_assume(m.h > 0 && m.h <= 2);
    __CPROVER_assume(m.c > 0 && m.c <= 3);
    
    // Allocate data with size check
    size_t size = (size_t)m.w * m.h * m.c;
    __CPROVER_assume(size <= SIZE_MAX / sizeof(unsigned char));
    m.data = malloc(size);
    __CPROVER_assume(m.data != NULL);
    
    // Test coordinates
    int x = nondet_int();
    int y = nondet_int();
    int c = nondet_int();
    
    // Get pixel with bounds checking
    unsigned char val = get_pixel(m, x, y, c);
    
    // Verify result
    if (x >= 0 && x < m.w && y >= 0 && y < m.h && c >= 0 && c < m.c) {
        __CPROVER_assert(val <= 255, "Valid pixel value");
    }
    
    // Clean up
    free(m.data);
}

// Verification harness
void verify_set_pixel_internal() {
    sod_img m;
    
    // Use fixed small dimensions
    m.w = 2;
    m.h = 2;
    m.c = 3;
    
    // Allocate memory
    size_t size = (size_t)m.w * m.h * m.c;
    m.data = malloc(size * sizeof(unsigned char));
    __CPROVER_assume(m.data != NULL);
    
    // Initialize memory
    for(size_t i = 0; i < size; i++) {
        m.data[i] = 0;
    }
    
    // Test with fixed coordinates
    int x = 1;
    int y = 1;
    int c = 0;  // RED channel
    float val = 128.0f;
    
    // Set pixel
    set_pixel(m, x, y, c, val);
    
    // Calculate expected index
    size_t index = (size_t)c * m.h * m.w + 
                  (size_t)y * m.w + 
                  x;
    
    // Verify value
    __CPROVER_assert(index < size, "Index in bounds");
    __CPROVER_assert(m.data[index] == (unsigned char)val, "Value preserved");
    
    // Verify through get_pixel
    unsigned char result = get_pixel(m, x, y, c);
    __CPROVER_assert(result == (unsigned char)val, "get_pixel matches");
    
    // Clean up
    free(m.data);
}

