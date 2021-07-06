class A {
private:
  int _count;

public:
  A() : _count() {}
  virtual ~A() {}
  int getCount() const { return _count; }
  void setCount(int count) { _count = count; }
  virtual void assign(const A& source) { _count = source._count; }
  virtual A* clone() const { return new A(*this); }
  A& operator=(const A& source) { assign(source); return *this; }
};

class B : public A {
public:
  B() {}

  virtual A* clone() const { return new B(*this); }
  B& operator=(const B& source) { assign(source); return *this; }
};

class C {
private:
  int _value;

public:
  C() : _value() {}
  virtual ~C() {}

};

class D : public B, public C {
private:
  bool _isValid;

public:
  D() {}

  virtual void assign(const A& asource)
    { B::assign(asource);
      const D& source = dynamic_cast<const D&>(asource);
      C::operator=(source);
      _isValid = source._isValid;
    }
  virtual A* clone() const { return new D(*this); }
};

int main() {
  D d;
  A& dref = d;
  A* d1 = dref.clone();
  D* dc = dynamic_cast<D*>(d1);
  C* c1 = dynamic_cast<C*>(d1);
  delete c1;
  return 0;
}


