/* run.config
OPT: @MACHDEP@ -deps -check -print
*/

//@ assigns \nothing;
extern int foo(void);

//@ assigns \result \from \nothing;
extern int bar(void);

//@ assigns \nothing \from \nothing;
extern int baz(void);

int main(void) {
	return foo()+bar()+baz();
}

 
