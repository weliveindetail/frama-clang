int x = 0;
int* f();

int main() {
  int *y = f();
  *y = 42;
  return 0;
}

int* f() { return &x; }
