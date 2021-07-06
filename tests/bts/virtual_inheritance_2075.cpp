struct A { }; 

struct B : public virtual A { }; 

struct D : public B {
	D(){}
};

