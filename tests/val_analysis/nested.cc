class A {
public:
  struct {
    int x;
    int y;
  } str;
  A() { str.x = 0; str.y = 0;};
};

int main() {
  A a;
  a.str.x = 1;
  return 0;
}
