/* run.config
OPT: @MACHDEP@ -cpp-extra-args="-DFOO" -print
OPT: @MACHDEP@ -cxx-clang-command="bin/framaCIRGen -DFOO" -print 
*/

#ifdef FOO
int foo() { return 2; }
#endif

int bar() { return 1; }
