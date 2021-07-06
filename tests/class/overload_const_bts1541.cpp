
class array {
	int elems[9]; 
	      int& operator[](int i)       { return elems[i]; } 
	const int& operator[](int i) const { return elems[i]; } 
};

