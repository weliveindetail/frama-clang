
int x;

void foo(void) {
	int x;
	x   = 2;
	::x = 3;
	//@ assert x   == 2;
	//@ assert ::x == 3;
}

