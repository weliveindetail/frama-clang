
/*@ allocates *a;
    frees *a;
    ensures \fresh{Pre,Here}(*a,1);
    ensures \freeable(*a);
    ensures \base_addr(*a) == (char*)(*a);
*/
void foo(int **a);

