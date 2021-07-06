
class A {
  public:
   int x;

   A() : x(0) {}
};

class B : public virtual A {
  public:
   B() { ++x; }
};

class C : public virtual A {
  public:
   C() { x += 3; }
};

class D : public B, public C {
  public:
   D() : B(), C(), A() { x += 4; }
};

int main(int argc, char** argv) {
   D d;
   return d.x;
}
