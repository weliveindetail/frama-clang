#include <cstdarg>

void foo(...) { return; }

int bar(int x = 0, ...) {
  int res = 0;
  va_list l;
  va_start(l,x);
  for (int i = 0; i<x ; i++) {
    res = va_arg(l,int);
  }
  return res;
}

int main() {
  int x = 0, y = 1;
  foo();
  foo(x);
  foo(x,y);
  bar();
  bar(0);
  bar(0,x,y);
  bar(1,x,y);
  bar(2,x,y);
  return 0;
}
