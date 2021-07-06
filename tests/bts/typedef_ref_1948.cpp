
class array {
	typedef int& reference; 

	int elems[5];

	//@ ensures \result == elems[i];
	reference foo(int i) { return elems[i]; }
};



