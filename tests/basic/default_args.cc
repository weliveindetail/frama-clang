struct A { };

int f(int x = 0, A a = A()) {
  return x;
}

int main() {
  int c = f();
  return 0;
}
