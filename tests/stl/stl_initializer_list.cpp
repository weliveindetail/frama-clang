#include <initializer_list>

void f() {
  int a[2] = {1,2};
  std::initializer_list<int> x (a,2);
}
