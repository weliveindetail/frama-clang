class A {
  int x;
public:
  A(): x(0) { };
  operator int () { x++; return x; }
  A(int& y) { x = ++y; };
};

int main () {
  A a;
  int x = (int)a;
  A b = (A)x;
  x = (int)b;
  return x;
}
