
/*@
	assigns *a;
	// comment 
*/
void swap_ptr(int* a) { }

// BTS 1819
/*@
	// Abracadabra! Mumbu-Jumbo! Contract magically disappear!
	requires size >= 1;
	ensures size == 5;
*/
void foo(int size) {
	//@ assert size >= 1; // comment
}

/*@ ensures \true;
// annotation comment without newline before ending annotation */
void bar() { }
