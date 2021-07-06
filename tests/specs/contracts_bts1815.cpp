/*@
	decreases n; // decrease clause in first line
	ensures \result == 1;
	assigns \nothing;
*/
int foo(int n) { return 1;}


/*@
        terminates \true;
	ensures \result == 1;
	decreases n; // decrease clause in second line
	assigns \nothing;
*/
int bar(int n) { return 1;}

/*@ behavior a:
     assumes n<=0;
     ensures \result == 0;
     behavior b:
     assumes n>0;
     ensures \result == 0;
     complete behaviors;
     disjoint behaviors;
     complete behaviors a,b;
     disjoint behaviors a,b;
*/
int baz(int n) { return 0; }
