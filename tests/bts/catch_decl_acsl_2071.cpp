
void foo(void) {
	try { throw(-2); }
	catch (int e) {
		if (e == -1) return;
		//@ assert e == -2;
	}
}

