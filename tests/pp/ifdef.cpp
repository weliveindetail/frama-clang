// Tests whether ifndef macros are properly handled
/*@

requires  \true;
#ifdef M
#  error "Failure"
#endif
#ifndef M
#	error "Failure3"
#endif

*/
void m() {}
