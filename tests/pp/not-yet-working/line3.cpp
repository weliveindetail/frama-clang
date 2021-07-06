// Tests a line directive with a comment after the number
/*@

requires  \true;
#line 101      // asdsadas
#error "Failure2"

*/
void m() {}
