

typedef unsigned int size_t;
/*@ predicate non_escaping{L}(void *s, size_t n) =
    \forall size_t i; 0 <= i < n ==> !\dangling((char*)s + i);
*/
