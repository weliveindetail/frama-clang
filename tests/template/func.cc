template<typename T> T* id(T* x) { return x; }

int main () {
  int x = 0;
  int *y = &x;
  int *z = id(y);
  return 0;
}
