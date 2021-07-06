struct A {
  static volatile int y;
};



int main () {
  int z = A::y;
  return 0;
}
