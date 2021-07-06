
template <int N>
class array {
	int elems[9];
};

template <int N>
class Stack {
	array<N> rep;
	//@ assigns rep.elems[0];
	void push() { }
};

Stack
	<6>
	s;


