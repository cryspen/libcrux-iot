# cmake -B build -G "Ninja Multi-Config"
# cmake --build build
# # For release (benchmarks)
# cmake --build build --config Release

cmake_minimum_required(VERSION 3.10..4.0)

project(libcrux-iot-sha3
    VERSION 0.1.0
    LANGUAGES C CXX
)

set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 20)

if(NOT MSVC)
     add_compile_options(
        -Wall

        # -Wextra
        # -pedantic
        # -Wconversion
        # -Wsign-conversion
        $<$<CONFIG:DEBUG>:-g>
        $<$<CONFIG:DEBUG>:-Og>
        $<$<CONFIG:RELEASE>:-g>
        $<$<CONFIG:RELEASE>:-O3>
    )
endif(NOT MSVC)

set(CMAKE_COLOR_DIAGNOSTICS "ON")

# For LSP-based editors
set(CMAKE_EXPORT_COMPILE_COMMANDS 1)
include_directories(
    ${PROJECT_SOURCE_DIR}
    ${PROJECT_SOURCE_DIR}/internal
    ${PROJECT_SOURCE_DIR}/karamel/include
)
file(GLOB SOURCES
  ${PROJECT_SOURCE_DIR}/libcrux_iot_sha3.c
  ${PROJECT_SOURCE_DIR}/libcrux_iot_core.c
)

if(${CMAKE_SYSTEM_NAME} MATCHES Linux)
    add_compile_options(
        -fPIC
    )
endif(${CMAKE_SYSTEM_NAME} MATCHES Linux)

# if(${CMAKE_SYSTEM_NAME} MATCHES Linux AND CMAKE_BUILD_TYPE MATCHES "Release")
#     add_compile_options(
#         -flto
#     )
#     add_link_options(-flto)
# endif(${CMAKE_SYSTEM_NAME} MATCHES Linux AND CMAKE_BUILD_TYPE MATCHES "Release")

add_library(sha3 SHARED ${SOURCES})
add_library(sha3_static STATIC ${SOURCES})

# This is only for local testing and we assume avx2 on x64.
if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|amd64|AMD64")
    message(STATUS "Detected an x64 architecture")
    add_compile_definitions(LIBCRUX_X64)
endif()

# --- Tests
# Get gtests
include(FetchContent)
FetchContent_Declare(googletest
    GIT_REPOSITORY https://github.com/google/googletest.git
    GIT_TAG v1.16.0
)

# For Windows: Prevent overriding the parent project's compiler/linker settings
set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)

# Get nlohmann json
FetchContent_Declare(json
    GIT_REPOSITORY https://github.com/nlohmann/json.git
    GIT_TAG v3.11.3
)
FetchContent_MakeAvailable(json)

add_executable(sha3_test
    ${PROJECT_SOURCE_DIR}/tests/sha3.cc
)
target_link_libraries(sha3_test PRIVATE
    sha3_static
    gtest_main
    nlohmann_json::nlohmann_json
)
