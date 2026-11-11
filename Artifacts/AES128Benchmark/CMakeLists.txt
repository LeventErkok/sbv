cmake_minimum_required(VERSION 3.20)
project(AES128Benchmark LANGUAGES C CXX)
set(CMAKE_C_STANDARD 99)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_C_FLAGS_RELEASE "-O3 -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE "-O3 -DNDEBUG")
set(CMAKE_INTERPROCEDURAL_OPTIMIZATION OFF)
set(BENCHMARK_ENABLE_TESTING OFF CACHE BOOL "" FORCE)
set(BENCHMARK_ENABLE_INSTALL OFF CACHE BOOL "" FORCE)
set(BENCHMARK_ENABLE_WERROR OFF CACHE BOOL "" FORCE)
add_subdirectory(vendor/benchmark EXCLUDE_FROM_ALL)
add_library(aes_impl STATIC
  generated/aes128BlockEncrypt.c generated/aes128KeySchedule.c
  vendor/tiny-AES-c/aes.c
  vendor/bearssl/src/symcipher/aes_common.c
  vendor/bearssl/src/symcipher/aes_big_enc.c)
target_include_directories(aes_impl PRIVATE vendor/bearssl/inc vendor/bearssl/src)
target_compile_definitions(aes_impl PUBLIC CBC=0 CTR=0 ECB=1 AES128=1)
add_executable(aes128_benchmark benchmark.cpp)
find_package(OpenSSL 3.0 REQUIRED COMPONENTS Crypto)
target_include_directories(aes128_benchmark PRIVATE generated vendor/tiny-AES-c)
target_link_libraries(aes128_benchmark PRIVATE aes_impl benchmark::benchmark OpenSSL::Crypto)
