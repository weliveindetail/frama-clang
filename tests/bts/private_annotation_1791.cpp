struct A
{
private:

    int i;

public:

    explicit A(int k) : i(k) {}

    /*@
      assigns \nothing;
      ensures \result == i;
    */
    int get() const
    {
        return i;
    }

};


int foo(const A& a)
{
    int b = a.get();
    //@ assert b == a.i;
    // Frama-Clang allows access to private field of A

    // a.i cannot be accessed here because it is private
    // this is recognized by Frama-Clang
    // int c = a.i;

    return b;
}
