/* run.config 
DONTRUN: issue remaining
*/

class Basic {
private:
  int _xxx;

public:
  Basic() : _xxx() {}
};

class A {
private:
  int _count;

public:
  A() : _count() {}
  int getCount() const { return _count; }
  void setCount(int count) { _count = count; }
  virtual void assign(const A& source) { _count = source._count; }
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
  virtual int foo() { return getCount(); }
  virtual int foo2() { return getCount(); }
  virtual int bar() { return getCount(); }
  B& operator=(const B& source) { assign(source); return *this; }
};

class C : public Basic, public A {
private:
  double _value;

public:
  C() : _value(1.0) { setCount(21); }

  virtual void assign(const A& source)
    { A::assign(source);
      _value = ((const C&) source)._value;
    }
  virtual int foo() { return getCount(); }
  virtual int foo2() { return getCount(); }
  virtual int bar2() { return getCount(); }
  C& operator=(const C& source) { assign(source); return *this; }
};

class D : public C, public B {
private:
  typedef B inherited;
  bool _isValid;

public:
  D() : _isValid(true) {}
  virtual void assign(const A& aSource)
    { inherited::assign(aSource);
      const D& source = (const D&) (const inherited&) aSource;
      C::assign((const C&) source);
      _isValid = source._isValid;
    }
  virtual int foo() { return inherited::getCount(); }
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
  b1.foo();
  b1.foo2();
  b1.bar();
  c1.foo();
  c1.foo2();
  c1.bar2();
  d1.foo();
  d1.bar();
  d1.bar2();
  a22 = a12; /* should fail */
  b2 = b1;
  c2 = c1; /* should fail */
  return 0;
}

