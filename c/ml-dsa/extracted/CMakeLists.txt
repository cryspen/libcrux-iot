# cmake -B build -G "Ninja Multi-Config"
# cmake --build build
# # For release (benchmarks)
# cmake --build build --config Release

cmake_minimum_required(VERSION 3.10..4.0)

project(libcrux-ml-dsa
    VERSION 0.1.0
    LANGUAGES C CXX
)

set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 20)

if(NOT MSVC)
    # TODO: Clean up
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
  ${PROJECT_SOURCE_DIR}/libcrux_iot_mldsa_core.c
  ${PROJECT_SOURCE_DIR}/libcrux_iot_sha3.c
  ${PROJECT_SOURCE_DIR}/libcrux_iot_mldsa65_portable.c
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

add_library(ml_dsa SHARED ${SOURCES})
add_library(ml_dsa_static STATIC ${SOURCES})

# --- Tests
if(DEFINED ENV{LIBCRUX_UNPACKED})
    add_compile_definitions(LIBCRUX_UNPACKED)
endif(DEFINED ENV{LIBCRUX_UNPACKED})

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

add_executable(ml_dsa_test65
    ${PROJECT_SOURCE_DIR}/tests/mldsa65.cc
)
target_link_libraries(ml_dsa_test65 PRIVATE
    ml_dsa_static
    gtest_main
    nlohmann_json::nlohmann_json
)

