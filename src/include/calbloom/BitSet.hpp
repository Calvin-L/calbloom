#pragma once

#include "calbloom/Slab.hpp"

#include <cstddef> // size_t
#include <climits> // CHAR_BIT


namespace calbloom {

/**
 * A fixed-size array of bits.
 *
 * This class duplicates the functionality of std::vector<bool>, with two big
 * improvements:
 *   - Faster initialization thanks to the internals of the Slab class.  (NOTE
 *     2020/11/25: hopefully someday std::vector<bool> implementations catch
 *     up, since there's no fundamental reason they can't.)
 *   - Unified get-then-set procedure that's a tad more compact than doing two
 *     separate calls to std::vector<bool>.
 */
class BitSet {

public:
  inline BitSet(std::size_t nbits);
  inline bool get(std::size_t i) const noexcept;
  inline bool getAndSet(std::size_t i, bool value) noexcept;

private:
  Slab data;

};


// ----------------------------------------------------------------------------


BitSet::BitSet(std::size_t nbits)
  : data((nbits + CHAR_BIT - 1) / CHAR_BIT) // https://stackoverflow.com/questions/33299093/how-to-perform-ceiling-division-in-integer-arithmetic
{
}

bool BitSet::get(std::size_t i) const noexcept {
  std::size_t byteIndex = i / CHAR_BIT;
  std::size_t bitIndex = i % CHAR_BIT;

  unsigned char bitmask = ((unsigned char)1) << bitIndex;
  return (data[byteIndex] & bitmask) != 0;
}

bool BitSet::getAndSet(std::size_t i, bool value) noexcept {
  std::size_t byteIndex = i / CHAR_BIT;
  std::size_t bitIndex = i % CHAR_BIT;

  unsigned char bitmask = ((unsigned char)1) << bitIndex;
  bool res = (data[byteIndex] & bitmask) != 0;

  if (value) {
    data[byteIndex] |= bitmask;
  } else {
    data[byteIndex] &= ~bitmask;
  }

  return res;
}

}
