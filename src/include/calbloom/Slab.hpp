#pragma once

#include <cassert>
#include <cstddef>


namespace calbloom {

/**
 * A fixed-size zero-initialized slab of memory.
 */
class Slab {
public:
  Slab(std::size_t nbytes);
  Slab(const Slab& other) = delete;
  Slab& operator=(const Slab& other) = delete;
  ~Slab() noexcept;
  inline unsigned char& operator[](std::size_t index) noexcept;
  inline unsigned char  operator[](std::size_t index) const noexcept;
private:
  std::size_t nbytes;
  unsigned char* data;
};


// ----------------------------------------------------------------------------


inline unsigned char& Slab::operator[](std::size_t index) noexcept {
  assert(index < nbytes);
  return data[index];
}

inline unsigned char Slab::operator[](std::size_t index) const noexcept {
  assert(index < nbytes);
  return data[index];
}

}
