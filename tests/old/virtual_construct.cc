class A {
protected:
  int _count;

public:
  virtual void incrementCounter() { ++_count; }
  virtual void decrementCounter() { ++_count; }

public:
  A() : _count() { incrementCounter(); }
  virtual ~A() { decrementCounter(); }
  int getCount() const { return _count; }
  void setCount(int count) { _count = count; }
  virtual void assign(const A& source) { _count = source._count; }
  virtual A* clone() const { return new A(*this); }
  A& operator=(const A& source) { assign(source); return *this; }
};

class B : public A {
public:
  virtual void incrementCounter() { _count += 10; }
  virtual void decrementCounter() { _count -= 10; }

public:
  B() { incrementCounter(); }
  virtual ~B() { decrementCounter(); }

  virtual A* clone() const { return new B(*this); }
  B& operator=(const B& source) { assign(source); return *this; }
};

int main() {
  B b;
  A& bref = b;
  A* b1 = bref.clone();
  b1->incrementCounter();
  delete b1;
  return 0;
}


