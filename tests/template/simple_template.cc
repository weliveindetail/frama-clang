template <typename T> T f(T* x) { return *x; };

int main () {
  int x = 0;
  bool y = true;
  f<int>(&x);
  f<bool>(&y);
  return 0;
}
