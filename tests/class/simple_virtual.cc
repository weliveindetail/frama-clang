class A {
private:
  int _count;

public:
  A() : _count() {}
  A(const A& source) : _count(source._count) {}

  virtual void assign(const A& source) { _count = source._count; }
  virtual A* clone() const { return new A(*this); }
  int getCount() const { return _count; }
  void setCount(int count) { _count = count; }
  A& operator=(const A& source) { assign(source); return *this; }
};

class B : public A {
private:
  char _ch;
public:
  B() : _ch('0') { setCount(42); }

  virtual void assign(const A& source)
    { A::assign(source);
      _ch = ((const B&) source)._ch;
    }
  virtual A* clone() const { return new B(*this); }
  B& operator=(const B& source) { assign(source); return *this; }
};

int main() {
  B b;
  A a;
  A& bref = b;
  A* ba = bref.clone();
  *ba = b;
  return 0;
}


