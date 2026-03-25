#include <stdio.h>
#include <stdlib.h>
#include <lean/lean.h>
#include <openssl/conf.h>
#include <openssl/evp.h>
#include <openssl/err.h>
#include <string.h>

// Encryption and decrption code adapted from the OpenSSL wiki
// https://wiki.openssl.org/index.php/EVP_Symmetric_Encryption_and_Decryption

void handleErrors(void)
{
    ERR_print_errors_fp(stderr);
    abort();
}

LEAN_EXPORT lean_obj_res enc_aes128_c (lean_obj_arg text256, lean_obj_arg iv128, lean_obj_arg key128) {
    EVP_CIPHER_CTX *ctx;
    int len;
    int ciphertext_len;
    unsigned char ciphertext[32];

    uint8_t *text = lean_sarray_cptr(text256);
    if (lean_sarray_size(text256) != 32) { abort(); }

    uint8_t *iv = lean_sarray_cptr(iv128);
    if (lean_sarray_size(iv128) != 16) { abort(); }

    uint8_t *key = lean_sarray_cptr(key128);
    if (lean_sarray_size(key128) != 16) { abort(); }

    if (!(ctx = EVP_CIPHER_CTX_new()))
        handleErrors();

    if (1 != EVP_EncryptInit_ex(ctx, EVP_aes_128_cbc(), NULL, key, iv))
        handleErrors();

    EVP_CIPHER_CTX_set_padding(ctx, 0);

    if (1 != EVP_EncryptUpdate(ctx, ciphertext, &len, text, 32))
        handleErrors();
    ciphertext_len = len;

    if (1 != EVP_EncryptFinal_ex(ctx, ciphertext + len, &len))
        handleErrors();
    ciphertext_len += len;

    EVP_CIPHER_CTX_free(ctx);

    lean_obj_res result = lean_alloc_sarray(1, ciphertext_len, ciphertext_len);
    uint8_t *out = lean_sarray_cptr(result);
    memcpy(out, ciphertext, ciphertext_len);

    lean_dec(text256);
    lean_dec(iv128);
    lean_dec(key128);

    return result;
}

LEAN_EXPORT lean_obj_res dec_aes128_c (lean_obj_arg cipher256, lean_obj_arg iv128, lean_obj_arg key128) {
    EVP_CIPHER_CTX *ctx;
    int len;
    int plaintext_len;
    unsigned char plaintext[32];

    uint8_t *ciphertext = lean_sarray_cptr(cipher256);
    if (lean_sarray_size(cipher256) != 32) { abort(); }

    uint8_t *iv = lean_sarray_cptr(iv128);
    if (lean_sarray_size(iv128) != 16) { abort(); }

    uint8_t *key = lean_sarray_cptr(key128);
    if (lean_sarray_size(key128) != 16) { abort(); }

    if (!(ctx = EVP_CIPHER_CTX_new()))
        handleErrors();

    if (1 != EVP_DecryptInit_ex(ctx, EVP_aes_128_cbc(), NULL, key, iv))
        handleErrors();

    EVP_CIPHER_CTX_set_padding(ctx, 0);

    if (1 != EVP_DecryptUpdate(ctx, plaintext, &len, ciphertext, 32))
        handleErrors();
    plaintext_len = len;

    if (1 != EVP_DecryptFinal_ex(ctx, plaintext + len, &len))
        handleErrors();
    plaintext_len += len;

    EVP_CIPHER_CTX_free(ctx);

    lean_obj_res result = lean_alloc_sarray(1, plaintext_len, plaintext_len);
    uint8_t *out = lean_sarray_cptr(result);
    memcpy(out, plaintext, plaintext_len);

    lean_dec(cipher256);
    lean_dec(iv128);
    lean_dec(key128);

    return result;
}

LEAN_EXPORT lean_obj_res sha256_c (lean_obj_arg input) {
    uint8_t *data = lean_sarray_cptr(input);
    size_t data_len = lean_sarray_size(input);

    unsigned char md[32];
    unsigned int md_len = 0;

    if (1 != EVP_Digest(data, data_len, md, &md_len, EVP_sha256(), NULL))
        handleErrors();

    lean_obj_res result = lean_alloc_sarray(1, 32, 32);
    uint8_t *out = lean_sarray_cptr(result);
    memcpy(out, md, 32);

    lean_dec(input);
    return result;
}
