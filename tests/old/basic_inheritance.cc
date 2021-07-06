class A {
private:
  int _count;

public:
  A() : _count() {}
  int getCount() const { return _count; }
  void setCount(int count) { _count = count; }
  void assign(const A& source) { _count = source._count; }
  A& operator=(const A& source) { assign(source); return *this; }
};

class B : public A {
private:
  char _ch;

public:
  B() : _ch('a') { setCount(42); }

  void assign(const A& source)
    { A::assign(source);
      _ch = ((const B&) source)._ch;
    }
  B& operator=(const B& source) { assign(source); return *this; }
};

class C : public A {
private:
  double _value;

public:
  C() : _value(1.0) { setCount(21); }

  void assign(const A& source)
    { A::assign(source);
      _value = ((const C&) source)._value;
    }
  C& operator=(const C& source) { assign(source); return *this; }
};

class D : public C, public B {
private:
  typedef B inherited;
  bool _isValid;

public:
  D() : _isValid(true) {}
  void assign(const A& aSource)
    { inherited::assign(aSource);
      const D& source = (const D&) (const inherited&) aSource;
      C::assign((const C&) source);
      _isValid = source._isValid;
    }
  D& operator=(const D& source) { assign((const inherited&) source); return *this; }
};

int main() {
  D d1, d2;
  d2 = d1;
  B &b1 = d1, &b2 = d2; 
  C &c1 = d1, &c2 = d2; 
  A &a11 = b1, &a21 = b2;
  A &a12 = c1, &a22 = c2;
  a21 = a11;
  a22 = a12;
  b2 = b1;
  c2 = c1;
  return 0;
}
