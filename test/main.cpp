#include <calbloom/BloomFilter.hpp>
#include <calbloom/ConcurrentBitSet.hpp>

#include <cassert>

template <class BloomFilter>
void test_bloom() {
  std::mt19937_64 generator;

  BloomFilter filter(1000000, 5, generator);

  assert(filter.insert(5));
  assert(!filter.insert(5));
  assert(filter.insert(6));
  assert(!filter.insert(6));
}

void test_cbs() {
  calbloom::ConcurrentBitSet cbs(100);
  assert(cbs.get(55) == 0);
  assert(cbs.getAndSet(55, true) == false);
  assert(cbs.getAndSet(55, true) == true);
  assert(cbs.getAndSet(55, true) == true);
  assert(cbs.getAndSet(55, false) == true);
  assert(cbs.getAndSet(55, false) == false);
}

int main() {
  test_bloom<calbloom::BloomFilter>();
  test_bloom<calbloom::ConcurrentBloomFilter>();
  test_cbs();
}
