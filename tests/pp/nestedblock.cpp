// Tests a nested block comment

/*@

requires x==0;/*@  ensures \true;

*/
void m(int x) {}
