// Tests a line directive with line and file
/*@

requires  \true;
#line 101 "TFILE"
#error "Failure2"

*/
void m() {}
