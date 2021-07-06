struct A {
  int x;
  A(): x(0) { }
  A(const A& a) { x = a.x + 1; }
};

/*@ behavior default: ensures \result.x == y; */
A f(int y) {
  A a;
  int z = y -1;
  a.x = z;
  return a;
}

/*@ behavior default: ensures \result == a.x; */
int g(A a) {
  return a.x;
}

int main() {
  A b = f(3);
  int z = g(b);
  /*@ assert z == b.x + 1; */
  return 0;
}
