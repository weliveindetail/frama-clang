
/*@ predicate compare_mem{L1,L2}(int* a, int *b) = \at(a,L1) == \at(a,L2);
    predicate foo(int *a) = \at(*a,L1) == 42;
 */

void iota(int val) {
	//@ assert \at(val,Pre) == 0;
	;
}

// Issue 1811 (referring to a C label)
void rot1(void) {
	int n = 0;
entry:
	//@ loop invariant 0 == \at(n,entry) == \at(n, Here);
	for (int i=0; i<9; i++)
		;
}
