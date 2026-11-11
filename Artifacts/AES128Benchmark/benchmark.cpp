#include <benchmark/benchmark.h>
#include <array>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <stdexcept>
#include <vector>
#include <openssl/evp.h>
#include <openssl/crypto.h>
#include <openssl/provider.h>

extern "C" {
#include "aes128Lib.h"
#include "aes.h"
// BearSSL's single-block primitive is internal. Link the unmodified source
// directly to avoid introducing a CBC/CTR mode into this comparison.
unsigned br_aes_keysched(uint32_t *, const void *, size_t);
void br_aes_big_encrypt(unsigned, const uint32_t *, void *);
}

using Block = std::array<uint8_t, 16>;
enum class Impl { SBV, BearSSL, TinyAES };

struct OpenSSLKey {
  EVP_CIPHER *cipher = EVP_CIPHER_fetch(nullptr, "AES-128-ECB", "provider=default");
  EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
  explicit OpenSSLKey(const Block &key) {
    if (!cipher || !ctx || EVP_EncryptInit_ex2(ctx, cipher, key.data(), nullptr, nullptr) != 1
        || EVP_CIPHER_CTX_set_padding(ctx, 0) != 1) {
      EVP_CIPHER_CTX_free(ctx); EVP_CIPHER_free(cipher);
      throw std::runtime_error("OpenSSL AES128 initialization failed");
    }
  }
  ~OpenSSLKey() { EVP_CIPHER_CTX_free(ctx); EVP_CIPHER_free(cipher); }
  OpenSSLKey(const OpenSSLKey &) = delete;
  OpenSSLKey &operator=(const OpenSSLKey &) = delete;
  bool encrypt(const void *in, void *out, int bytes) {
    int written = 0;
    return EVP_EncryptUpdate(ctx, static_cast<unsigned char *>(out), &written,
                            static_cast<const unsigned char *>(in), bytes) == 1
        && written == bytes;
  }
};

static uint32_t load_be(const uint8_t *p) {
  return (uint32_t(p[0]) << 24) | (uint32_t(p[1]) << 16)
       | (uint32_t(p[2]) << 8) | uint32_t(p[3]);
}
static void store_be(uint8_t *p, uint32_t x) {
  p[0] = uint8_t(x >> 24); p[1] = uint8_t(x >> 16);
  p[2] = uint8_t(x >> 8); p[3] = uint8_t(x);
}

struct Keys {
  uint32_t sbv[44], bear[60];
  unsigned rounds;
  AES_ctx tiny;
  explicit Keys(const Block &key) {
    uint32_t words[4], dec[44];
    for (unsigned i = 0; i < 4; ++i) words[i] = load_be(key.data() + 4*i);
    aes128KeySchedule(words, sbv, dec);
    rounds = br_aes_keysched(bear, key.data(), key.size());
    AES_init_ctx(&tiny, key.data());
  }
};

template<Impl I>
static inline void encrypt(const Keys &k, const Block &in, Block &out) {
  if constexpr (I == Impl::SBV) {
    uint32_t pt[4], ct[4];
    for (unsigned i = 0; i < 4; ++i) pt[i] = load_be(in.data() + 4*i);
    aes128BlockEncrypt(pt, k.sbv, ct);
    for (unsigned i = 0; i < 4; ++i) store_be(out.data() + 4*i, ct[i]);
  } else {
    std::memcpy(out.data(), in.data(), 16);
    if constexpr (I == Impl::BearSSL)
      br_aes_big_encrypt(k.rounds, k.bear, out.data());
    else
      AES_ECB_encrypt(&k.tiny, out.data());
  }
}

static void check(const Block &key, const Block &pt, const Block *expected) {
  Keys keys(key);
  Block a, b, c, d;
  OpenSSLKey openssl(key);
  encrypt<Impl::SBV>(keys, pt, a);
  encrypt<Impl::BearSSL>(keys, pt, b);
  encrypt<Impl::TinyAES>(keys, pt, c);
  if (!openssl.encrypt(pt.data(), d.data(), 16) || a != b || a != c || a != d
      || (expected && a != *expected))
    throw std::runtime_error("AES128 ciphertext validation failed");
}

static uint32_t random_word(uint32_t &s) {
  s ^= s << 13; s ^= s >> 17; s ^= s << 5; return s;
}
static void validate() {
  const Block key = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15};
  const Block pt = {0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
                    0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff};
  const Block ct = {0x69,0xc4,0xe0,0xd8,0x6a,0x7b,0x04,0x30,
                    0xd8,0xcd,0xb7,0x80,0x70,0xb4,0xc5,0x5a};
  check(key, pt, &ct);
  uint32_t seed = 0x534256;
  for (unsigned n = 0; n < 1024; ++n) {
    Block k, p;
    for (unsigned i = 0; i < 16; ++i) {
      k[i] = uint8_t(random_word(seed)); p[i] = uint8_t(random_word(seed));
    }
    check(k, p, nullptr);
  }
  // Check multi-block calls and continued use of the same EVP context.
  Keys keys(key);
  OpenSSLKey openssl(key);
  for (size_t count : {size_t(1), size_t(64), size_t(1024)}) {
    std::vector<Block> input(count), expected(count), output(count);
    for (size_t i = 0; i < count; ++i) {
      for (auto &byte : input[i]) byte = uint8_t(random_word(seed));
      encrypt<Impl::SBV>(keys, input[i], expected[i]);
    }
    for (unsigned repeat = 0; repeat < 3; ++repeat)
      if (!openssl.encrypt(input.data(), output.data(), int(count * 16)) || output != expected)
        throw std::runtime_error("OpenSSL bulk/reused-context validation failed");
    // The native-word SBV path must agree with the byte-oriented adapter.
    std::vector<std::array<uint32_t, 4>> words(count), cipher(count);
    for (size_t i = 0; i < count; ++i)
      for (unsigned w = 0; w < 4; ++w) words[i][w] = load_be(input[i].data() + 4*w);
    for (size_t i = 0; i < count; ++i) {
      aes128BlockEncrypt(words[i].data(), keys.sbv, cipher[i].data());
      Block bytes;
      for (unsigned w = 0; w < 4; ++w) store_be(bytes.data() + 4*w, cipher[i][w]);
      if (bytes != expected[i])
        throw std::runtime_error("SBV native-word validation failed");
    }
  }
  std::cout << "Validation passed: FIPS-197 AES128 vector and 1024 "
               "deterministic differential cases across all four implementations; "
               "OpenSSL bulk, reused-context, and SBV native-word checks at all three buffer sizes.\n";
}

template<bool Bulk>
static void openssl_reused_key(benchmark::State &state) {
  const Block key = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15};
  OpenSSLKey keys(key);
  const size_t blocks = size_t(state.range(0)) / 16;
  std::vector<Block> input(blocks), output(blocks);
  uint32_t seed = 0x534256;
  for (auto &block : input)
    for (auto &byte : block) byte = uint8_t(random_word(seed));
  // Force any lazy setup before timing as well.
  if (!keys.encrypt(input.data(), output.data(), int(state.range(0)))) {
    state.SkipWithError("OpenSSL warmup failed"); return;
  }
  for (auto _ : state) {
    benchmark::DoNotOptimize(input.data());
    if constexpr (Bulk) {
      if (!keys.encrypt(input.data(), output.data(), int(state.range(0)))) {
        state.SkipWithError("OpenSSL encryption failed"); break;
      }
    } else {
      for (size_t i = 0; i < blocks; ++i)
        if (!keys.encrypt(input[i].data(), output[i].data(), 16)) {
          state.SkipWithError("OpenSSL encryption failed"); break;
        }
    }
    benchmark::DoNotOptimize(output.data());
    benchmark::ClobberMemory();
  }
  state.SetBytesProcessed(state.iterations() * state.range(0));
  state.SetItemsProcessed(state.iterations() * int64_t(blocks));
}

template<Impl I>
static void reused_key(benchmark::State &state) {
  // Google Benchmark excludes setup before the range-for from timing.
  const Block key = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15};
  const Keys keys(key);
  const size_t blocks = size_t(state.range(0)) / 16;
  std::vector<Block> input(blocks), output(blocks);
  uint32_t seed = 0x534256;
  for (auto &block : input)
    for (auto &byte : block) byte = uint8_t(random_word(seed));
  for (auto _ : state) {
    benchmark::DoNotOptimize(input.data());
    for (size_t i = 0; i < blocks; ++i) encrypt<I>(keys, input[i], output[i]);
    benchmark::DoNotOptimize(output.data());
    benchmark::ClobberMemory();
  }
  state.SetBytesProcessed(state.iterations() * state.range(0));
  state.SetItemsProcessed(state.iterations() * int64_t(blocks));
}

// SBV's generated function takes and returns 32-bit words. Converting the shared
// input bytes to words happens before timing, so this isolates the generated code
// from the byte-order adapter used by the other SBV row.
static void sbv_native_words(benchmark::State &state) {
  const Block key = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15};
  const Keys keys(key);
  const size_t blocks = size_t(state.range(0)) / 16;
  std::vector<std::array<uint32_t, 4>> input(blocks), output(blocks);
  uint32_t seed = 0x534256;
  for (auto &block : input) {
    Block bytes;
    for (auto &byte : bytes) byte = uint8_t(random_word(seed));
    for (unsigned w = 0; w < 4; ++w) block[w] = load_be(bytes.data() + 4*w);
  }
  for (auto _ : state) {
    benchmark::DoNotOptimize(input.data());
    for (size_t i = 0; i < blocks; ++i)
      aes128BlockEncrypt(input[i].data(), keys.sbv, output[i].data());
    benchmark::DoNotOptimize(output.data());
    benchmark::ClobberMemory();
  }
  state.SetBytesProcessed(state.iterations() * state.range(0));
  state.SetItemsProcessed(state.iterations() * int64_t(blocks));
}

int main(int argc, char **argv) {
  try { validate(); }
  catch (const std::exception &e) { std::cerr << e.what() << '\n'; return 1; }
  if (argc == 2 && std::strcmp(argv[1], "--validate-only") == 0) return 0;
  benchmark::RegisterBenchmark("SBV", &reused_key<Impl::SBV>)
      ->Arg(16)->Arg(1024)->Arg(16384);
  benchmark::RegisterBenchmark("SBV_native_words", &sbv_native_words)
      ->Arg(16)->Arg(1024)->Arg(16384);
  benchmark::RegisterBenchmark("BearSSL_big", &reused_key<Impl::BearSSL>)
      ->Arg(16)->Arg(1024)->Arg(16384);
  benchmark::RegisterBenchmark("tiny_AES_c", &reused_key<Impl::TinyAES>)
      ->Arg(16)->Arg(1024)->Arg(16384);
  benchmark::RegisterBenchmark("OpenSSL_EVP_block", &openssl_reused_key<false>)
      ->Arg(16)->Arg(1024)->Arg(16384);
  benchmark::RegisterBenchmark("OpenSSL_EVP_bulk", &openssl_reused_key<true>)
      ->Arg(16)->Arg(1024)->Arg(16384);
  benchmark::Initialize(&argc, argv);
  benchmark::AddCustomContext("openssl_version", OpenSSL_version(OPENSSL_VERSION));
  benchmark::AddCustomContext("openssl_build", OpenSSL_version(OPENSSL_CFLAGS));
  benchmark::AddCustomContext("openssl_cpu_info", OpenSSL_version(OPENSSL_CPU_INFO));
  OpenSSLKey info(Block{});
  benchmark::AddCustomContext("openssl_provider",
      OSSL_PROVIDER_get0_name(EVP_CIPHER_get0_provider(info.cipher)));
  if (benchmark::ReportUnrecognizedArguments(argc, argv)) return 1;
  benchmark::RunSpecifiedBenchmarks();
  benchmark::Shutdown();
}
