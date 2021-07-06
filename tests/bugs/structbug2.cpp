/* run.config
DONTRUN: see structbug.cpp for more information
*/

typedef int td;
struct tm { int x; };
class tc  { int y; };
union tu  { int z; float f; };

// The following line should give an error message, or at least a warning
//@ predicate m(class td s) = \true;
