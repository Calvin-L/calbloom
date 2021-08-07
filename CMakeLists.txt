# -----------------------------------------------------------------------------
# Project Setup

# NOTE: need CMake 3.9+ to specify project description:
#   https://cmake.org/cmake/help/latest/release/3.9.html?highlight=project%20description#commands
# Need 3.11 for FetchContent
# Need 3.14 for FetchContent_MakeAvailable
cmake_minimum_required(VERSION 3.14)
project(CalvinsBloomFilter
    VERSION 1.0
    DESCRIPTION "A simple bloom filter implementation"
    LANGUAGES CXX)

# -----------------------------------------------------------------------------
# Deps

include(FetchContent)
FetchContent_Declare(
    caluhash_repo
    GIT_REPOSITORY https://github.com/Calvin-L/caluhash.git
    GIT_TAG        main)
FetchContent_MakeAvailable(caluhash_repo)

# -----------------------------------------------------------------------------
# Library

set(CALBLOOM_HEADER_FILES
    src/include/calbloom/BitSet.hpp
    src/include/calbloom/BloomFilter.hpp
    src/include/calbloom/Slab.hpp)
add_library(calbloom_objects OBJECT
    ${CALBLOOM_HEADER_FILES}
    src/Slab.cpp)
add_library(calbloom SHARED
    $<TARGET_OBJECTS:calbloom_objects>)
add_library(calbloom_static STATIC
    $<TARGET_OBJECTS:calbloom_objects>)

target_link_libraries(calbloom_objects PRIVATE caluhash)
target_include_directories(calbloom_objects PRIVATE src/include)
target_compile_features(calbloom_objects PRIVATE cxx_std_11) # need <random>

target_link_libraries(calbloom PUBLIC caluhash)
target_include_directories(calbloom PUBLIC src/include)
target_compile_features(calbloom PUBLIC cxx_std_11) # need <random>

target_link_libraries(calbloom_static PUBLIC caluhash)
target_include_directories(calbloom_static PUBLIC src/include)
target_compile_features(calbloom_static PUBLIC cxx_std_11) # need <random>

# -----------------------------------------------------------------------------
# Testing

enable_testing()

add_executable(calbloom_test test/main.cpp)
target_link_libraries(calbloom_test PRIVATE calbloom_static)
add_test(NAME calbloom_test COMMAND calbloom_test)

add_executable(calbloom_example test/example.cpp)
target_link_libraries(calbloom_example PRIVATE calbloom_static)
add_test(NAME calbloom_example COMMAND calbloom_example)

# -----------------------------------------------------------------------------
# Install  (I feel that this should be automatic given just the list of
# targets, but CMake requires us to explicitly list the things we want
# installed.)

install(TARGETS calbloom calbloom_static
    LIBRARY  DESTINATION ${CMAKE_INSTALL_LIBDIR}
    INCLUDES DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})

# Absolute idiocy.  Why is there no canonical, out-of-the-box way to declare
# a public include directory?
install(
    FILES ${CALBLOOM_HEADER_FILES}
    DESTINATION include/calbloom)
