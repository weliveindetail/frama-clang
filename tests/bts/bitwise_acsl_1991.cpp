
/*@ requires (i|i) <= 8;
    ensures (i==i) | i; 
    ensures i | (i==i);
*/
void foo(int i);

