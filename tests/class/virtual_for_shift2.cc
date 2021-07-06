class A {
private:
  int _count;

public:
  A() : _count() {}
  virtual ~A() {}
  int getCount() const { return _count; }
  void setCount(int count) { _count = count; }
  virtual void assign(const A& source) { _count = source._count; }
  virtual int compare(const A& source) const
    { return _count < source._count ? -1 : (_count >source._count ? 1 : 0); }
  A& operator=(const A& source) { assign(source); return *this; }
};

class B : public A {
private:
  char _ch;

public:
  B() : _ch('a') { setCount(42); }

  virtual void assign(const A& source)
    { A::assign(source);
      _ch = ((const B&) source)._ch;
    }
  B& operator=(const B& source)
   {  assign(*(const A*) &source); return *this; }
};

class C : public B {
private:
  double _value;

public:
  C() : _value(1.0) { setCount(21); }

  virtual void assign(const A& source)
    { A::assign(source);
      _value = ((const C*) &source)->_value;
    }
  C& operator=(const C& source) { assign(*(const A*) &source); return *this; }
};

int main() {
  C c1, c2;
  c1 = c2;
  return c1.compare(*(const A*) &c2);
}

