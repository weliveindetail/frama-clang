class A {
  int x;
public:
  A() : x() {}
};

class B : public A {
  int y;
public:
  B() : y() {}
};

int main() {
  B b;
  A* pa = &b;
  B* pb = (B*) pa;
}

