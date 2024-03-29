
/*@
    assigns *a, *b;

    ensures *a == \old(*b);
    ensures *b == \old(*a);
*/
inline
void swap_ptr(int* a, int* b)
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

/*@
    assigns a, b;

    ensures a == \old(b);
    ensures b == \old(a);
*/
inline
void swap(int& a, int& b)
{
    int tmp = a;
    a = b;
    b = tmp;
}

/*@
    assigns a, b;

    ensures a == \old(b);
    ensures b == \old(a);
*/
inline
void swap(short& a, short& b)
{
    short tmp = a;
    a = b;
    b = tmp;
}


/*@
    assigns a, b;

    ensures a == \old(b);
    ensures b == \old(a);
*/
template<typename T>
void swap(T& a, T& b)
{
    T tmp = a;
    a = b;
    b = tmp;
}

// #include <cstddef> // need this for unsigned long and long



template<typename T, unsigned long N>




class array
{
public:



    //@ logic bool operator==(array b) =  \forall integer i; 0 <= i < n ==> elems[i] = b.elem[i];

    typedef T& reference;

    typedef const T& const_reference;

    typedef unsigned long size_type;

    typedef long difference_type;

    typedef T value_type;

    typedef T* pointer;

    typedef const T* const_pointer;

    typedef pointer iterator;

    typedef const_pointer  const_iterator;

private:
    T elems[N];

public:

    /*@
        assigns elems[0..N-1];

    */
    //  ensures \forall integer i; 0 <= i < N; elems[i] == T();
    array() : elems() {}

    /*@
        assigns elems[0..N-1];
    */
    //  ensures *this == a; /* invalid implicit conversion */
    array(const array& a)
    {
        for(unsigned long i = 0; i < size(); ++i)
            elems[i] = a[i];
    }

    /*@
        assigns elems[0..N-1];
    */
    //  ensures *this == a;
    //  ensures \result == *this;
    /* invalid implicit conversion */
    array& operator=(const array& a)
    {
        for(unsigned long i = 0; i < size(); ++i)
            elems[i] = a[i];

        return *this;
    }

    /*@
        assigns \nothing;
    */
    ~array() {}

    /*@
        assigns \nothing;

        ensures \result == N;
    */
    unsigned long size() const
    {
        return N;
    }

    /*@
        assigns \nothing;

        ensures \result == N;
    */
    unsigned long max_size() const
    {
        return N;
    }

    /*@
        assigns \nothing;

        ensures \result == (N == 0) ? true : false;
    */
    bool empty() const
    {
        return size() == 0;
    }

    /*
       requires i < size(); // not able to call methods, even get methods

       assigns \result \from this, i;

       ensures \result == elems[i]; // unknown implicit conversion ?
    */
    reference operator[](unsigned long i)
    {
        return elems[i];
    }

    /*@
       requires i < size(); // not able to call methods, even get methods

       assigns \result \from this, i;

    */
    // ensures \result == elems[i]; // unknown implicit conversion ?
    const_reference operator[](unsigned long i) const
    {
        return elems[i];
    }

    /*@
        assigns elems[0..N-1];

        ensures \forall integer i; 0 <= i < N ==> elems[i] == u;
    */
    void fill(const T& u)
    {
        for(unsigned long i = 0; i < size(); ++i)
            elems[i] = u;
    }

    /*@
        assigns elems[0..N-1];
        assigns y.elems[0..N-1];

        ensures *this == \old(y);
        ensures  y    == \old(*this);
    */
    void swap(array& y)
    {
        for(unsigned long i = 0; i < N; ++i)
            ::swap(elems[i], y[i]); // array::swap hides ::swap
    }

    /*@
         require N > 0;

         assigns \nothing;

         ensures \result == &(elems[0]);
         ensures \valid(\result+(0..N-1));
    */
    T* data()
    {
        return &(elems[0]);
    }

    /*@
         require N > 0;

         assigns \nothing;

         ensures \result == &(elems[0]);
    */
    const T* data() const
    {
        return &(elems[0]);
    }


    /*@
        assigns \nothing;

    */
    //  ensures \result == &(elems[0]); //invalid implicit conversion ?
    //  ensures \valid(\result+(0..N-1)); // invalid operands to binary addition
    iterator begin()
    {
        return elems;
    }

    /*@
        assigns \nothing;

    */
    //  ensures \result == &(elems[N]); //invalid implicit conversion ?
    //  ensures \valid(\result+(-N..-1)); // invalid operands to binary addition
    iterator end()
    {
        return elems + N;
    }

    /*@
        assigns \nothing;

    */
    //  ensures \result == &(elems[0]);  //invalid implicit conversion ?
    //  ensures \valid_read(\result+(0..N-1)); // invalid operands to binary addition
    const_iterator begin() const
    {
        return elems;
    }

    /*@
         assigns \nothing;

    */
    //  ensures \result == &(elems[N]);  //invalid implicit conversion ?
    //  ensures \valid_read(\result+(-N..-1)); // invalid operands to binary addition

    const_iterator end()const
    {
        return elems + N;
    }

};

/*@
    assigns \nothing;

    ensures (\result == true) <==> a == b;
 */
template <typename T, unsigned long N>
bool operator==(const array<T, N>& a, const array<T, N>&  b)
{
    for(unsigned long i = 0; i < a.size(); ++i)
    {
        if(a[i] != b[i])
            return false;
    }

    return true;
}



/*@
    assigns \nothing;

    ensures (\result == true) <==> a != b;
 */
template<typename T, unsigned long N>
bool operator !=(const array<T, N>& a, const array<T, N>& b)
{
    return !(a == b);
}



template <typename T, unsigned long N>
class Stack
{ // parse the annotations after the declarations!
private:

    array<T, N> rep;

    unsigned long sz;
public:

    typedef unsigned long size_type;

    typedef T value_type;

    //  logic T Top() = rep[sz-1]; // subscripted value is neither array nor pointer

    /*@ logic integer Size() = sz;

        logic integer Capacity() = N;

        logic bool operator==(Stack s) = Size() == Size(s) && (\forall integer i; 0 <= i < Size() ==> rep[i] == s.rep[i]);

        strong class invariant StackInvariant() = sz <= N;

        predicate Empty() = Size() == 0;

        predicate Full() = Size() == Capacity();

    */

    /*@
        assigns \nothing;

    */
    //  ensures (\result == true) <==> (*this == b); // unknown identifier 'b'
    bool operator==(const Stack& s) const
    {
        if(size() == s.size() )
        {
            for(unsigned long i = 0; i < size(); i++)
            {
                if(rep[i] != s.rep[i] )
                    return false;
            }

            return true;
        }

        return false;
    }

    /*@
      assigns rep, sz;

    */
    //  ensures Empty();
    Stack() : rep(), sz(0) { }

    /*@
       assigns rep,sz;

       ensures *this == s;
    */
    Stack(const Stack& s) : rep(s.rep) , sz(s.sz) {}

    /*@
       assigns \nothing;
    */
    ~Stack() {}

    /*@
         assigns rep, sz;

         ensures *this == s;
         ensures \result ==*this;
    */
    Stack& operator =(const Stack& s )
    {
        rep = s.rep;
        sz  = s.sz;
        return *this;
    }

    /*@
         assigns \nothing;

    */
    //   ensures (\result == true) <==> Empty();
    bool empty()const
    {
        return size() ==  0;
    }

    /*@
         assigns \nothing;

    */
    //   ensures (\result == true) <==> Full();
    bool full() const
    {
        return size() == capacity();
    }

    /*@
         assigns \nothing;

    */
    //   ensures \result == Capacity();
    unsigned long capacity() const
    {
        return rep.size();
    }

    /*@
         assigns \nothing;

    */
    //   ensures \result == Size();
    unsigned long size() const
    {
        return sz;
    }

    //  requires !Empty();
    /*@

        assigns \nothing;

    */
    //  ensures \result == Top();
    const T& top() const
    {
        return rep[sz - 1];
    }
    //  requires !Full();
    /*

        assigns rep[sz], sz;

        ensures Size() == Size{Old}()+1;
        ensures Top() == x;
    */
    void push(const T& x)
    {
        if(!full())
            rep[sz++] = x;
    }

    //  requires !Empty();
    /*@

        assigns sz;

    */
    //  ensures Size() == Size{Old}()-1;
    void pop()
    {
        if(!empty())
            --sz;
    }

};

/*@
    assign \nothing;

    ensures (\result == \true) <==> a != b;
*/
template <typename T, unsigned long N>
bool operator!=(const Stack<T, N>& a, const Stack<T, N>& b)
{
    return !(a == b);
}


Stack<int, 6> s;

