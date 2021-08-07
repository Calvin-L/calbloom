# Calvin's Bloom Filter Library

This is a dirt-simple [Bloom filter](https://en.wikipedia.org/wiki/Bloom_filter)
for C++.

## How to use this library

```c++
#include <calbloom/BloomFilter.hpp>
#include <random>
#include <cassert>

int main() {

    // Source of randomness.  Pick your favorite from <random>!
    std::mt19937_64 generator;

    // Construct a new Bloom filter with the given parameters.
    int nbuckets = 100000;
    int nhashes = 4;
    BloomFilter filter(nbuckets, nhashes, generator);

    filter.add(10);

    assert(!filter.might_contain(9));
    assert(filter.might_contain(10));
    assert(!filter.might_contain(11));

    return 0;
}
```

See also: `test/main.cpp`.

## How to include this library in your project

If you use CMake:

```cmake
cmake_minimum_required(VERSION 3.14) # or higher

...

include(FetchContent)
FetchContent_Declare(
    calbloom_repo
    GIT_REPOSITORY https://github.com/Calvin-L/calbloom.git
    GIT_TAG        main)
FetchContent_MakeAvailable(calbloom_repo)

...

target_link_libraries(YOUR_TARGET_HERE PRIVATE calbloom)
```

Note that you may want to replace `main` with a specific revision for stable
builds.
