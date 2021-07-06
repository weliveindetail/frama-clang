enum foo {
  a,
  x = 2,
  y = x + 1
};

int main() {
  foo b = y;
  return 0;
}
