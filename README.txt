Running CBMC On This Repo

I used Windows Visual Studio and ran on the Developer Command Prompt Line 

Verify_Invert
cbmc picprocess.c picture.c utils.c --function verify_invert --unwind 4 --no-unwinding-assertions --memory-leak-check --drop-unused-functions

Verify_Rotate_Picture (Takes a Few Minutes)
cbmc picprocess.c picture.c utils.c --function verify_rotate_picture --unwind 4 --no-unwinding-assertions --memory-leak-check --drop-unused-functions

Verify_Flip_Picture (Takes a Few Minutes)
cbmc picprocess.c picture.c utils.c --function verify_flip_picture --unwind 4 --no-unwinding-assertions --memory-leak-check --drop-unused-functions

Verify_Blur_Picture (Takes a Few Minutes)
cbmc picprocess.c picture.c utils.c --function verify_blur_picture --unwind 4 --no-unwinding-assertions --memory-leak-check --drop-unused-functions

Verify_Grayscale
cbmc picprocess.c picture.c utils.c --function verify_grayscale --unwind 4 --no-unwinding-assertions --memory-leak-check --drop-unused-functions

Verify Get_Pixel
cbmc picture.c --function get_pixel --unwind 4 --drop-unused-functions

Verify Set_Pixel (Property Specific)
cbmc picprocess.c picture.c utils.c --function verify_invert --unwind 4 --no-unwinding-assertions --memory-leak-check --drop-unused-functions --property set_pixel.assertion.1 --property set_pixel.assertion.2 --property set_pixel.assertion.3

Somewhat Clean Looking At Trace 
cbmc picprocess.c picture.c utils.c --function verify_invert --unwind 4 --no-unwinding-assertions --memory-leak-check --trace --stop-on-fail | grep -E "rgb.blue|verify.blue|pic.height|pic.width|rgb.green|verify.green|rgb.red|verify.red"

Unsure Work On Concurrency (Uses fences and atomic properties)
cbmc threadlist.c --function verify_thread_list --unwind 4 --drop-unused-functions
