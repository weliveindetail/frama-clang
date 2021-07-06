// Tests whether error PP directive with macro is properly reported
// Note that arguments of error and warning directives are not macro-expanded
/*@

requires  \true;
	#  error M      __LINE__

*/
void m() {}
