class A {
private:
  int _count;

public:
  A() : _count() {}
  virtual ~A() {}

  int getCount() const { return _count; }
  void setCount(int count) { _count = count; }
  virtual A* clone() const { return new A(*this); }
  virtual void assign(const A& source) { _count = source._count; }
  A* createCopy() const { return clone(); }
  A& operator=(const A& source) { assign(source); return *this; }
};

class B : public virtual A {
private:
  char _ch;

public:
  B() : _ch('a') { setCount(42); }

  virtual A* clone() const { return new B(*this); }
  virtual void assign(const A& source)
    { A::assign(source);
      _ch = dynamic_cast<const B&>(source)._ch;
    }
  B* createCopy() const { return dynamic_cast<B*>(clone()); }
  B& operator=(const B& source) { assign(source); return *this; }
};

class C : public virtual A {
private:
  double _value;

public:
  C() : _value(1.0) { setCount(21); }

  virtual A* clone() const { return new C(*this); }
  virtual void assign(const A& source)
    { A::assign(source);
      _value = dynamic_cast<const C&>(source)._value;
    }
  C* createCopy() const { return dynamic_cast<C*>(clone()); }
  C& operator=(const C& source) { assign(source); return *this; }
};

class D : public B, public C {
private:
  typedef B inherited;
  bool _isValid;

public:
  D() : A(), _isValid(true) {}
  virtual A* clone() const { return (B*) new D(*this); }
  virtual void assign(const A& asource)
    { inherited::assign(asource);
      C::assign(asource);
      const D& source = dynamic_cast<const D&>(asource);
      _isValid = source._isValid;
    }
  bool isValid() const { return _isValid; }
  D* createCopy() const { return dynamic_cast<D*>(clone()); }
  D& operator=(const D& source) { assign(source); return *this; }
};

int main() {
  D d;
  D* newd = d.createCopy();
  A* a1 = (B*) newd;
  A* a2 = (C*) newd;
  bool isTrue = a1 == a2;
  return 0;
}

