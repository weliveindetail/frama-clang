typedef int INT;

/*@ type invariant foo (INT x) = x >= 3; */

INT x = 3;

int main () { x++; return 0; }
