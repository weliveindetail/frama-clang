struct A {
constexpr A(bool b) : m(b?42:43) { }
int m;
};

int f(int c) {
switch (c) {
  case A(true).m: return 0;
  case A(false).m: return 1;
  default: return 2;
 }
}
