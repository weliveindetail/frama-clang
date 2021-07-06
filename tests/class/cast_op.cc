class A {
  int x;
public:
  A(): x(0) { };
  operator int () { x++; return x; }
};

int main () {
  A a;
  int x = (int)a;
  return x;
}
