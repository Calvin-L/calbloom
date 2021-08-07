#include "calbloom/Slab.hpp"

#include <new>


// IMPLEMENTATION NOTE
// On Linux/BSD/Darwin, anonymous mmap is an *insanely* good way to implement
// the Slab interface.  In particular, the data is zero-initialized lazily,
// so we can allocate a Slab almost instantly without paying the cost to memset
// all the memory to zero.
extern "C" {
#include <sys/mman.h>
}


static_assert(sizeof(unsigned char) == 1, "sizeof(unsigned char) != 1");

// mmap man page says "The fd argument is ignored; however, some
// implementations require fd to be -1 if MAP_ANONYMOUS"
static constexpr int MMAP_FD = -1;

// mmap man page says "MAP_ANONYMOUS [...] The offset argument should be zero"
static constexpr off_t MMAP_OFFSET = 0;

calbloom::Slab::Slab(std::size_t n)
  : nbytes(n),
    data((unsigned char*)mmap(
      nullptr,
      nbytes,
      PROT_READ | PROT_WRITE,
      MAP_ANONYMOUS | MAP_PRIVATE,
      MMAP_FD,
      MMAP_OFFSET)) {
  if (data == nullptr) {
    throw std::bad_alloc();
  }
}

calbloom::Slab::~Slab() noexcept {
  if (data != nullptr) {
    munmap(data, nbytes);
  }
}
