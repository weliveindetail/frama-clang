template <class T> T foo(T x) { return x; }

int main () {
  long x;
  void* y = foo((void*)x);
  return 0;
}
