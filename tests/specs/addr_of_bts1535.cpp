
int elems[9];

/*@ ensures \result == &(elems[1]);
    ensures *(elems+1) == 0;
 */
int *data() { return &elems[1]; }

