struct A {
  private:
  int v;
  /*@ghost int w; */
  int x;
  /*@ ghost int y; */
public:
  /*@ class invariant model: x == y; */
  A(): v(0) /*@ghost, w(0)*/, x(0) /*@ ghost , y(0) */ { }
  A(int x): v(0) /*@ghost, w(0), y(0)*/, x(x) { }
  A& incr() { x++; /*@ghost y++; */ return *this; }
};

int main() {
  A a;
  a.incr().incr().incr();
  return 0;
}
