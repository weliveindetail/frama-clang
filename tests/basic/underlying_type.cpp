#include <type_traits>

enum class E : int { A = 1, B = 2 };

int f() {
  return static_cast<std::underlying_type<E>::type>(E::A);
}
