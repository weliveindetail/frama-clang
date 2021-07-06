
/*@
	requires size >= 1;
	This certainly is a syntactical error.
	ensures size == 4;
	ensures size == 5;
*/
void foo(int size) {
	//@ assert size >= 1;
}

