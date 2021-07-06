// Tests whether ifdef macros are handled properly
# define M 0
/*@

requires  \true;
#  ifndef M
#	error "Failure3"
#  endif
#  ifdef M
#  error "Failure"
#  endif

*/
void m() {}
