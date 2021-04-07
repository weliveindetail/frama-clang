/* run.config
   DONTRUN:
*/

#include "static_1.hpp"

int Sm::cache = 42;

static int x;

int Sm_get(void)
{
    static int y = 1337;
    y++;
    x = 42;
    return Sm::cache;
}

