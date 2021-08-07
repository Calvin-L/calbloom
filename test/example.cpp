// This is the example from the README, verbatim.

#include <calbloom/BloomFilter.hpp>
#include <random>
#include <cassert>

int main() {

    // Source of randomness.  Pick your favorite from <random>!
    std::mt19937_64 generator;

    // Construct a new Bloom filter with the given parameters.
    int nbuckets = 100000;
    int nhashes = 4;
    calbloom::BloomFilter filter(nbuckets, nhashes, generator);

    bool isNew = filter.insert(10);
    assert(isNew);

    isNew = filter.insert(10);
    assert(!isNew);

    assert(!filter.mightContain(9));
    assert(filter.mightContain(10));
    assert(!filter.mightContain(11));

    return 0;
}
