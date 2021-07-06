
class Cl { public: int a; };

//@ logic bool equalCl(Cl x,Cl y) =       (x.a == y.a);
          bool equalCl(Cl x,Cl y) { return x.a == y.a; }


