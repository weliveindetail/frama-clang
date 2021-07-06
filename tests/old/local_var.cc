#define CC_SCOPE
#include "cxx_builtin.cc"

struct A { int x; ~A () { x++; } };

int main () {
  A* x;
  {
    A a;
    a.x = 1;
    x = &a;
  }
  x -> x = 2;
  return 0;
}
