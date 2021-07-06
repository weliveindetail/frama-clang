
class A {};
class B : public A {};
class C : virtual public A {};
class D : public B, public C {};

