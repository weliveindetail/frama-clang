#include <cstddef>

int main() {
  int* x = NULL;
  int y = 0;
  x = &y;
  return *x;
}
