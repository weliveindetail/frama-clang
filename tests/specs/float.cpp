/* run.config
OPT: @MACHDEP@ -check -print -float-hex @CXX@
*/

//@ ensures \result == 0.4;
float foo(void);

//@ ensures \result == 0x1.ap-1;
float bar(void);

//@ ensures \result == 0.5f;
float bla(void);
