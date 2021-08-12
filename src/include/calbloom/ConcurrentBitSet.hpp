#pragma once

#include <cstddef> // size_t
#include <climits> // CHAR_BIT
#include <atomic>
#include <memory>


namespace calbloom {

/**
 * A fixed-size array of bits.
 *
 * This class provides thread-safe, atomic implementations of the same methods
 * as BitSet.
 */
class ConcurrentBitSet {

public:
  inline ConcurrentBitSet(std::size_t nbits);
  inline bool get(std::size_t i) const noexcept;
  inline bool getAndSet(std::size_t i, bool value) noexcept;

private:
  // TODO: if anyone would ever support C++20, we could use
  // std::atomic_unsigned_lock_free here...
  using AtomicWord = std::atomic<unsigned int>;
  using Word = unsigned int;
  static constexpr std::size_t BITS_PER_WORD = sizeof(Word) * CHAR_BIT;
  std::unique_ptr<AtomicWord[]> data;

};


// ----------------------------------------------------------------------------


ConcurrentBitSet::ConcurrentBitSet(std::size_t nbits)
  : data(new AtomicWord[(nbits + BITS_PER_WORD - 1) / BITS_PER_WORD]) // https://stackoverflow.com/questions/33299093/how-to-perform-ceiling-division-in-integer-arithmetic
{
  // FINGERS CROSSED that this loop turns into some vector operations after a
  // puff of inlining and optimization.  We use std::atomic_init because this
  // initialization does not need to be thread-safe.
  AtomicWord* ptr = data.get();
  constexpr unsigned int zero = 0;
  for (std::size_t i = 0; i < (nbits + BITS_PER_WORD - 1) / BITS_PER_WORD; ++i) {
    std::atomic_init(ptr + i, zero);
  }
}

bool ConcurrentBitSet::get(std::size_t i) const noexcept {
  std::size_t byteIndex = i / BITS_PER_WORD;
  std::size_t bitIndex = i % BITS_PER_WORD;

  Word bitmask = ((Word)1) << bitIndex;

  return (data[byteIndex].load() & bitmask) != 0;
}

bool ConcurrentBitSet::getAndSet(std::size_t i, bool value) noexcept {
  std::size_t byteIndex = i / BITS_PER_WORD;
  std::size_t bitIndex = i % BITS_PER_WORD;

  Word bitmask = ((Word)1) << bitIndex;

  Word oldVal =
    value
      ? data[byteIndex].fetch_or(bitmask)
      : data[byteIndex].fetch_and(~bitmask);

  return (oldVal & bitmask) != 0;
}

}
