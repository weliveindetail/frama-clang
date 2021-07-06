
struct tm { int x; };
class tc  { int y; };
union tu  { int z; float f; };

//@ predicate m(class tc s) = \true;
//@ predicate m(struct tm s) = \true;
//@ predicate m(union tu s) = \true;

//@ predicate m(struct    // Intended error
