
//@ ensures 42 <= \result;
int foo(int n) {
	if (n < 42)
		throw 1;
	else
		return n;
}

//@ ensures 24 <= \result;
int bar(int n) {
	try {
		return foo(n);
	} 
	catch (...) {
		return 31;
	}
}
		
