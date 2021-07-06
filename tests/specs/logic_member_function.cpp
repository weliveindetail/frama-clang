// From BTS 1727

class A
{
public:

    //@ logic int V() = val;


    A() : val(0) {}

    explicit A(int v) : val(v) {}

    /*@
        assigns val;

        ensures val == a.val;

        ensures \result.V() == a.val;

        ensures V() == a.V();

        ensures \result == *this;
    */
    A& operator=(const A& a)
    {
        val = a.val;

        return *this;
    }

    int value() const
    {
        return val;
    }

private:

    int val;
};

union U {
  //@ predicate foo () = i == 0;
  int i;
};

/*@ assigns x;
    ensures x.i == 0; */
void g(union U& x) {
  x.i = 0;
}

/*@ assigns x; 
    ensures x.foo(); */
void h(union U& x) {
x.i = 0;
}
