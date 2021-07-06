
/*
	Taken from
	stackoverflow.com/questions/189172/c-templates-turing-complete
*/

template <int N> struct Factorial {
	enum { val = Factorial<N-1>::val * N };
};

template <> struct Factorial<0> {
	enum { val = 1 };
};

int main() { return Factorial<6>::val + Factorial<5>::val; }
