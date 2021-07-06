/* run.config
   OPT: @EVA@ -slice-assert ::f -slice-callers -slice-print -journal-disable
*/
struct A {
  int x;
  int y;
  A() : x(0), y(1) {}
};

int g() { return 0; }

void f(A& a) {
  a.x = 42;
  while (a.y) {
    a.y--;
  }
  //@ assert a.x != 0;
}

int main() {
  A a;
  a.y = 4;
  f(a);
  return 0;
}
