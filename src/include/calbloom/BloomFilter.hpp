#pragma once

#include <caluhash.hpp>
#include <calbloom/BitSet.hpp>
#include <calbloom/ConcurrentBitSet.hpp>

#include <cstddef>
#include <vector>


namespace calbloom {

template <class Bits>
class GenericBloomFilter {

public:
  template <class Rng>
  GenericBloomFilter(std::size_t m, unsigned k, Rng& sourceOfRandomness);

  template <class T>
  bool insert(const T& x) noexcept;

  template <class T>
  bool mightContain(const T& x) const noexcept;

private:
  uint64_t nbits;
  std::vector<caluhash::HashFunction> hashFunctions;
  Bits bits;

};

using BloomFilter = GenericBloomFilter<BitSet>;
using ConcurrentBloomFilter = GenericBloomFilter<ConcurrentBitSet>;


// ----------------------------------------------------------------------------


template <class Bits>
template <class Rng>
GenericBloomFilter<Bits>::GenericBloomFilter(std::size_t m, unsigned k, Rng& sourceOfRandomness) : nbits(m), bits(m) {
  hashFunctions.reserve(k);
  for (size_t i = 0; i < k; ++i) {
    hashFunctions.emplace_back(sourceOfRandomness, 64);
  }
}

template <class Bits>
template <class T>
bool GenericBloomFilter<Bits>::insert(const T& x) noexcept {
  bool isNew = false;

  for (const auto& h : hashFunctions) {
    uint64_t hash = h(x) % nbits;
    bool oldBit = bits.getAndSet(hash, true);
    isNew = isNew || !oldBit;
  }

  return isNew;
}

template <class Bits>
template <class T>
bool GenericBloomFilter<Bits>::mightContain(const T& x) const noexcept {
  for (const auto& h : hashFunctions) {
    uint64_t hash = h(x) % nbits;
    if (!bits.get(hash)) {
      return false;
    }
  }

  return true;
}

}
