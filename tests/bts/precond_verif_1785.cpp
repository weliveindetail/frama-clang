
class A
{
    int x;

public:

    /*@
        assigns x;
        ensures x == v;
    */
    explicit A(int v) : x(v) {}

    // first version straightforward

    /*@
        assigns x;
        ensures \result == *this;
        ensures x == a.x;
        ensures \result.x == a.x;
        ensures a.x == \old(a.x);
    */
    A& operator=(const A& a)
    {
        x = a.x;
        return *this;
    }

    // second version with different argument type and potential name clash

    /*@
        assigns this->x;
        ensures \result == *this;
        ensures this->x == x;
        ensures \result.x == x;
    */
    A& operator=(int x)
    {
        this->x = x;
        return *this;
    }

    /*@
        assigns \nothing;
        ensures \result == x;
        ensures x == \old(x);
    */
    int get() const { return x; }

};



/*@
    assigns a;
    ensures a.x == x;
    ensures \result == \old(a.x);
*/
int foo(A& a, int x)
{
    int old_value = a.get();
    //@ assert old_value == \at(a.x, Pre);

    A a1(x);
    a = a1;
    return old_value;
}

