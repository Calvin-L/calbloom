#include <calbloom/BloomFilter.hpp>

int main() {

  std::mt19937_64 generator;

  calbloom::BloomFilter filter(1000000, 5, generator);

  assert(filter.insert(5));
  assert(!filter.insert(5));
  assert(filter.insert(6));
  assert(!filter.insert(6));

}
