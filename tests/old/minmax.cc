#include "cxx_builtin.cc"
int main() {
  int x = 0;
  int y = 2;
  int z = std::min(x, y);
  z++;
  int t = std::max(y, x);
  x = std::max(x, y);
  return 0;
}
