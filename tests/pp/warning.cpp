// Tests whether warning PP directive with macro is properly reported
// Note that arguments of error and warning directives are not macro-expanded
/*@

ensures  \true;
	#  warning M		 __LINE__

*/
void m() {}
