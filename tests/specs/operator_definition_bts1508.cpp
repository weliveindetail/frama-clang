class Cl { public: int a; };

//@ logic bool operator==(Cl x,Cl y) =       (x.a == y.a);
          bool operator==(Cl x,Cl y) { return x.a == y.a; }
