class A {
private:
  int _count;

protected:
  static A* castFromCopy(A* source) { return source; }
  static A* castToCopy(A* source) { return source; }
  static const A* castFromCopy(const A* source) { return source; }
  static const A* castToCopy(const A* source) { return source; }

public:
  A() : _count() {}
  virtual ~A() {}

  int getCount() const { return _count; }
  void setCount(int count) { _count = count; }
  virtual A* clone() const { return new A(*this); }
  virtual void assign(const A& source) { _count = source._count; }
  A* createCopy() const { return castFromCopy(clone()); }
  A& operator=(const A& source) { assign(source); return *this; }
};

class B : public A {
private:
  char _ch;

protected:
  static B* castFromCopy(A* source) { return (B*) source; }
  static A* castToCopy(B* source) { return source; }
  static const B* castFromCopy(const A* source) { return (const B*) source; }
  static const A* castToCopy(const B* source) { return source; }

public:
  B() : _ch('a') { setCount(42); }

  virtual A* clone() const { return castToCopy(new B(*this)); }
  virtual void assign(const A& source)
    { A::assign(source);
      _ch = (castFromCopy(&source))->_ch;
    }
  B* createCopy() const { return castFromCopy(clone()); }
  B& operator=(const B& source) { assign(*castToCopy(&source)); return *this; }
};

class C : public A {
private:
  double _value;

protected:
  static C* castFromCopy(A* source) { return (C*) source; }
  static A* castToCopy(C* source) { return source; }
  static const C* castFromCopy(const A* source) { return (const C*) source; }
  static const A* castToCopy(const C* source) { return source; }

public:
  C() : _value(1.0) { setCount(21); }

  virtual A* clone() const { return castToCopy(new C(*this)); }
  virtual void assign(const A& source)
    { A::assign(source);
      _value = (castFromCopy(&source))->_value;
    }
  C* createCopy() const { return castFromCopy(clone()); }
  C& operator=(const C& source) { assign(*castToCopy(&source)); return *this; }
};

class D : public B, public C {
private:
  typedef B inherited;
  bool _isValid;

protected:
  static D* castFromCopy(A* source) { return (D*) inherited::castFromCopy(source); }
  static A* castToCopy(D* source) { return inherited::castToCopy(source); }
  static const D* castFromCopy(const A* source) { return (const D*) inherited::castFromCopy(source); }
  static const A* castToCopy(const D* source) { return inherited::castToCopy(source); }

public:
  D() : _isValid(true) {}
  virtual A* clone() const { return castToCopy(new D(*this)); }
  virtual void assign(const A& asource)
    { inherited::assign(asource);
      const D& source = *castFromCopy(&asource);
      C::assign((const C&) source);
      _isValid = source._isValid;
    }
  bool isValid() const { return _isValid; }
  D* createCopy() const { return castFromCopy(clone()); }
  D& operator=(const D& source) { assign(*castToCopy(&source)); return *this; }
};

class E : public D {
private:
  typedef D inherited;
  unsigned short _bitField;

protected:
  static E* castFromCopy(A* source) { return (E*) inherited::castFromCopy(source); }
  static A* castToCopy(E* source) { return inherited::castToCopy(source); }
  static const E* castFromCopy(const A* source) { return (const E*) inherited::castFromCopy(source); }
  static const A* castToCopy(const E* source) { return inherited::castToCopy(source); }

public:
  E() : _bitField(13) {}

  virtual A* clone() const { return castToCopy(new E(*this)); }
  virtual void assign(const A& asource)
    { inherited::assign(asource);
      const E& source = *castFromCopy(&asource);
      _bitField = source._bitField;
    }
  E* createCopy() const { return castFromCopy(clone()); }
  E& operator=(const E& source) { assign(*castToCopy(&source)); return *this; }
};

class F : public D {
private:
  typedef D inherited;
  float _errorBound;

protected:
  static F* castFromCopy(A* source) { return (F*) inherited::castFromCopy(source); }
  static A* castToCopy(F* source) { return inherited::castToCopy(source); }
  static const F* castFromCopy(const A* source) { return (const F*) inherited::castFromCopy(source); }
  static const A* castToCopy(const F* source) { return inherited::castToCopy(source); }

public:
  F() : _errorBound(0.01) {}

  virtual A* clone() const { return castToCopy(new F(*this)); }
  virtual void assign(const A& asource)
    { inherited::assign(asource);
      const F& source = *castFromCopy(&asource);
      _errorBound = source._errorBound;
    }
  F* createCopy() const { return castFromCopy(clone()); }
  F& operator=(const F& source) { assign(*castToCopy(&source)); return *this; }
};

class G : public E, public F {
private:
  typedef E inherited;

protected:
  static G* castFromCopy(A* source) { return (G*) inherited::castFromCopy(source); }
  static A* castToCopy(G* source) { return inherited::castToCopy(source); }
  static const G* castFromCopy(const A* source) { return (const G*) inherited::castFromCopy(source); }
  static const A* castToCopy(const G* source) { return inherited::castToCopy(source); }

public:
  G() {}
  G* createCopy() const { return castFromCopy(clone()); }
  virtual A* clone() const { return castToCopy(new G(*this)); }
  virtual void assign(const A& asource)
    { inherited::assign(asource);
      const G& source = *castFromCopy(&asource);
      F::assign(*F::castToCopy(&source));
    }
  G& operator=(const G& source) { assign(*castToCopy(&source)); return *this; }
};

int main() {
  G g;
  G* newg = g.createCopy();
  A* a1 = (B*) (E*) newg;
  A* a2 = (C*) (E*) newg;
  A* a3 = (B*) (F*) newg;
  A* a4 = (C*) (F*) newg;
  bool isTrue = dynamic_cast<B*>(a1) == dynamic_cast<B*>(a2);
  isTrue = dynamic_cast<C*>(a1) == dynamic_cast<C*>(a2);
  isTrue = dynamic_cast<B*>(a3) != dynamic_cast<B*>(a2);
  isTrue = dynamic_cast<E*>(a1) == dynamic_cast<E*>(a3);
  F f;
  F* newf = f.createCopy();
  A* a5 = (B*) newf;
  isTrue = !dynamic_cast<E*>(a5);
  return 0;
}

