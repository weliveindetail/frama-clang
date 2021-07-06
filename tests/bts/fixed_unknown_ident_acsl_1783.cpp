class A
{
    int x;

public:

    /*@
        // y is unknown here and should be rejected
        ensures \result.x == y;
    */
    A& operator=(int x)
    {
        this->x = x;
        return *this;
    }

};

/*@
    ensures \result == b;
*/
int foo(int a)
{
    return a;
}
