
class Cl {
public:
	int a;

//  logic bool     non0(Cl x);
          bool     non0(Cl x);

};

//@ logic bool Cl::non0(Cl x) =        x.a != 0;
          bool Cl::non0(Cl x) { return x.a != 0; }

