#include "shipovnik.h"
#include "genvector.h"
#include "params.h"
#include "randombytes.h"
#include "sign.h"
#include "syndrome.h"
#include "utils.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <openssl/sha.h>

void sha512_f(const uint8_t *message, size_t msg_len, uint8_t *hash) {
    SHA512(message, msg_len, hash);
}

void shipovnik_generate_keys(uint8_t *sk, uint8_t *pk) {
    ALLOC_ON_STACK(uint16_t, s, N);
    gen_vector(s);
    for (size_t i = 0; i < N; ++i) {
        size_t j = i / 8;
        sk[j] <<= 1;
        sk[j] |= s[i] & 1;
    }
    syndrome(H_PRIME, sk, pk);
}

#define SIGMA_Y_SIZE (SIGMA_PACKED_BYTES + SHIPOVNIK_PUBLICKEYBYTES)

void shipovnik_sign(const uint8_t *sk, const uint8_t *msg, size_t msg_len,
                    uint8_t *sig, size_t *sig_len) {

    ALLOC_ON_STACK(uint64_t, shuf64_, N);
    ALLOC_ON_STACK(uint32_t, entropy32_, N);
    ALLOC_ON_STACK(uint8_t, sigma_y_, SIGMA_Y_SIZE);
    ALLOC_ON_STACK(uint8_t, u1_, SHIPOVNIK_SECRETKEYBYTES);
    ALLOC_ON_STACK(uint8_t, u2_, SHIPOVNIK_SECRETKEYBYTES);

    ALLOC_ON_STACK(uint8_t, h, SHA512_OUTPUT_BYTES);
    ALLOC_ON_STACK(uint8_t, b, DELTA);

    uint8_t *const us = malloc(DELTA * SHIPOVNIK_SECRETKEYBYTES);
    uint16_t *const sigmas = malloc(DELTA * SIGMA_BYTES);

    for (size_t i = 0; i < DELTA; i++) {
        uint8_t *u = us + i * SHIPOVNIK_SECRETKEYBYTES;
        uint16_t *sigma = sigmas + i * N;
        for (uint16_t j = 0; j < N; ++j) {
            sigma[j] = j;
        }

        uint8_t *ebytes = (uint8_t *)entropy32_;
        randombytes(u, SHIPOVNIK_SECRETKEYBYTES);
        randombytes(ebytes, N * sizeof(uint32_t));
        shuffle(entropy32_, sigma, shuf64_, N);

        uint8_t *ci = sig + i * 3 * SHA512_OUTPUT_BYTES;

        pack_sigma(sigma, N, sigma_y_);
        uint8_t *y = sigma_y_ + SIGMA_PACKED_BYTES;
        syndrome(H_PRIME, u, y);
        sha512_f(sigma_y_, SIGMA_Y_SIZE, ci);

        apply_permutation(sigma, u, u1_, N);
        sha512_f(u1_, SHIPOVNIK_SECRETKEYBYTES,
                       ci + SHA512_OUTPUT_BYTES);

        bitwise_xor(u, sk, SHIPOVNIK_SECRETKEYBYTES, u1_);
        apply_permutation(sigma, u1_, u2_, N);
        sha512_f(u2_, SHIPOVNIK_SECRETKEYBYTES,
                       ci + 2 * SHA512_OUTPUT_BYTES);
    }

    uint8_t *const msg_cs = malloc(msg_len + CS_BYTES);
    memcpy(msg_cs, msg, msg_len);
    memcpy(msg_cs + msg_len, sig, CS_BYTES);
    sha512_f(msg_cs, msg_len + CS_BYTES, h);
    free(msg_cs);

    const multiword_number_t mwh = h_3_delta_shift(h, SHA512_OUTPUT_BYTES);
    if (NULL == mwh) {
        goto cleanup;
    }

    if (h_to_ternary_vec(mwh, b, DELTA)) {
        goto cleanup;
    }

    uint8_t *rs = sig + CS_BYTES;
    *sig_len = CS_BYTES;
    for (size_t i = 0; i < DELTA; i++) {
        uint8_t *u = us + i * SHIPOVNIK_SECRETKEYBYTES;
        uint16_t *sigma = sigmas + i * N;
        switch (b[i]) {
        case 0:
            pack_sigma(sigma, N, rs);
            rs += SIGMA_PACKED_BYTES;
            memcpy(rs, u, SHIPOVNIK_SECRETKEYBYTES);
            rs += SHIPOVNIK_SECRETKEYBYTES;
            *sig_len += SIGMA_PACKED_BYTES + SHIPOVNIK_SECRETKEYBYTES;
            break;
        case 1:
            pack_sigma(sigma, N, rs);
            rs += SIGMA_PACKED_BYTES;
            bitwise_xor(u, sk, SHIPOVNIK_SECRETKEYBYTES, rs);
            rs += SHIPOVNIK_SECRETKEYBYTES;
            *sig_len += SIGMA_PACKED_BYTES + SHIPOVNIK_SECRETKEYBYTES;
            break;
        case 2:
            apply_permutation(sigma, u, rs, N);
            rs += SHIPOVNIK_SECRETKEYBYTES;
            apply_permutation(sigma, sk, rs, N);
            rs += SHIPOVNIK_SECRETKEYBYTES;
            *sig_len += 2 * SHIPOVNIK_SECRETKEYBYTES;
            break;
        default:
            goto cleanup;
        }
    }

cleanup:
    free(us);
    free(sigmas);
    multiword_number_free(mwh);
}

int shipovnik_verify(const uint8_t *pk, const uint8_t *sig, const uint8_t *msg,
                     size_t msg_len) {

    ALLOC_ON_STACK(uint8_t, h, SHA512_OUTPUT_BYTES);
    ALLOC_ON_STACK(uint8_t, b, DELTA);
    ALLOC_ON_STACK(uint16_t, sigma, N);

    ALLOC_ON_STACK(uint8_t, sigma_y_, SIGMA_Y_SIZE)
    ALLOC_ON_STACK(uint8_t, u_1, SHIPOVNIK_SECRETKEYBYTES);
    ALLOC_ON_STACK(uint8_t, cij_, SHA512_OUTPUT_BYTES);

    const size_t c_border = CS_BYTES;
    uint8_t *buff_mc = malloc(sizeof(uint8_t) * (msg_len + c_border));

    memcpy(buff_mc, msg, msg_len);
    memcpy(buff_mc + msg_len, sig, c_border);

    sha512_f(buff_mc, msg_len + c_border, h);

    int ret = 0;
    multiword_number_t mwh = h_3_delta_shift(h, SHA512_OUTPUT_BYTES);
    if (NULL == mwh) {
        ret = 1;
        goto cleanup;
    }

    if (h_to_ternary_vec(mwh, b, DELTA)) {
        ret = 1;
        goto cleanup;
    }

    const uint8_t *ci0_true = NULL, *ci1_true = NULL, *ci2_true = NULL;
    const uint8_t *ri0 = NULL, *ri1 = NULL;
    const uint8_t *ci = sig;
    const uint8_t *ri = sig + c_border;
    size_t weight = 0;
    for (size_t i = 0; i < DELTA; i++) {
        ci0_true = ci;
        ci1_true = ci + SHA512_OUTPUT_BYTES;
        ci2_true = ci + 2 * SHA512_OUTPUT_BYTES;
        ci += 3 * SHA512_OUTPUT_BYTES;
        switch (b[i]) {
        case 0: {
            ri0 = ri;
            ri1 = ri + SIGMA_PACKED_BYTES;
            ri += SIGMA_PACKED_BYTES + SHIPOVNIK_SECRETKEYBYTES;

            memcpy(sigma_y_, ri0, SIGMA_PACKED_BYTES);
            syndrome(H_PRIME, ri1, sigma_y_ + SIGMA_PACKED_BYTES);
            sha512_f(sigma_y_, SIGMA_Y_SIZE, cij_);
            if (memcmp(ci0_true, cij_, SHA512_OUTPUT_BYTES)) {
                ret = 1;
                goto cleanup;
            }

            if (unpack_sigma(ri0, SIGMA_PACKED_BYTES, sigma) != 0) {
                ret = 1;
                goto cleanup;
            }
            apply_permutation(sigma, ri1, u_1, N);
            sha512_f(u_1, SHIPOVNIK_SECRETKEYBYTES, cij_);

            if (memcmp(ci1_true, cij_, SHA512_OUTPUT_BYTES)) {
                ret = 1;
                goto cleanup;
            }

            break;
        }
        case 1: {
            ri0 = ri;
            ri1 = ri + SIGMA_PACKED_BYTES;
            ri += SIGMA_PACKED_BYTES + SHIPOVNIK_SECRETKEYBYTES;

            memcpy(sigma_y_, ri0, SIGMA_PACKED_BYTES);
            uint8_t *y = sigma_y_ + SIGMA_PACKED_BYTES;
            syndrome(H_PRIME, ri1, y);
            bitwise_xor(y, pk, SHIPOVNIK_PUBLICKEYBYTES, y);
            sha512_f(sigma_y_, SIGMA_Y_SIZE, cij_);
            if (memcmp(ci0_true, cij_, SHA512_OUTPUT_BYTES)) {
                ret = 1;
                goto cleanup;
            }

            if (unpack_sigma(ri0, SIGMA_PACKED_BYTES, sigma) != 0) {
                ret = 1;
                goto cleanup;
            }
            apply_permutation(sigma, ri1, u_1, N);
            sha512_f(u_1, SHIPOVNIK_SECRETKEYBYTES, cij_);

            if (memcmp(ci2_true, cij_, SHA512_OUTPUT_BYTES)) {
                ret = 1;
                goto cleanup;
            }

            break;
        }
        case 2: {
            ri0 = ri;
            ri1 = ri + SHIPOVNIK_SECRETKEYBYTES;
            ri += 2 * SHIPOVNIK_SECRETKEYBYTES;

            memcpy(u_1, ri0, SHIPOVNIK_SECRETKEYBYTES);
            sha512_f(u_1, SHIPOVNIK_SECRETKEYBYTES, cij_);
            if (memcmp(ci1_true, cij_, SHA512_OUTPUT_BYTES)) {
                ret = 1;
                goto cleanup;
            }

            bitwise_xor(ri0, ri1, SHIPOVNIK_SECRETKEYBYTES, u_1);
            sha512_f(u_1, SHIPOVNIK_SECRETKEYBYTES, cij_);
            if (memcmp(ci2_true, cij_, SHA512_OUTPUT_BYTES)) {
                ret = 1;
                goto cleanup;
            }

            count_bits(ri1, SHIPOVNIK_SECRETKEYBYTES, &weight);
            if (W != weight) {
                ret = 1;
                goto cleanup;
            }

            break;
        }
        default: {
            ret = 1;
            goto cleanup;
        }
        }
    }

cleanup:
    free(buff_mc);
    multiword_number_free(mwh);
    return ret;
}