#include <lean/lean.h>
#include <sodium.h>

lean_obj_res lean_randombytes_buf(uint32_t size) {
    if (sodium_init() < 0) {
        lean_internal_panic("libsodium initialization failed");
    }
    
    lean_object* arr = lean_mk_empty_byte_array(lean_box((size_t)size));
    uint8_t* ptr = lean_sarray_cptr(arr);
    randombytes_buf(ptr, (size_t)size);
    lean_sarray_set_size(arr, (size_t)size);
    
    return lean_io_result_mk_ok(arr);
}
