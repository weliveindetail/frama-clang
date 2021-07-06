struct A
{
   int n;
};

typedef struct A B;

/*@
    requires \valid(b);
    assigns \nothing;
    ensures \result == b->n;
*/
int foo(B* b)
{
    return b->n;
}
