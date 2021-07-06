/* run.config
   GCC:
   OPT: tests/basic/static_1_aux.cpp -print -check -cxx-c++stdlib-path share/libc++ -cxx-clang-command="bin/framaCIRGen"
*/


// clang++ -Weverything init.cpp sm.cpp && ./a.out
// tis-analyzer-gui --no-libc -64 -val -cxx-keep-mangling init.cpp sm.cpp

#include "static_1.hpp"

extern "C" int printf(const char *, ...);

static int x;

int main(void)
{
    x = 43;
    printf("MARK %d %d\n", Sm_get(), Sm::cache);
    return 0;
}


