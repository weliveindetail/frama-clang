int x = 0;

class A {
  int y;
public:
  A () { x++; y = 1;}
  ~A () { x--; }
};

int main() {
  A* a = new A();
  delete(a);
  return 0;
}
