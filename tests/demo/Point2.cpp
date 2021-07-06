#ifndef INT_MIN
#define INT_MIN ((int) (1U << 32))
#endif
#ifndef INT_MAX
#define INT_MAX ((int) (~0U >> 1))
#endif

class Point2
{
private:

    int x;
    int y;

public:

    //@ logic bool operator==(Point2 b) = x == b.x && y == b.y;

    Point2() : x(), y() {}

    /*@
        assigns x;
        assigns y;

        ensures this->x == a;
        ensures y == b;
    */
    Point2(int a, int b = 0) : x(a), y(b) {}

    /*@
        assigns x, y;

        ensures *this == p; // logical equality
    */
    Point2(const Point2& p)
    {
        x = p.x;
        y = p.y;
    }

    /*@
        // ??
    */
    ~Point2()
    {
    }

    /*@
        assigns \nothing;

        ensures *this == p; // logical equality defined by us
        ensures \result == *this;
    */
    Point2& operator=(const Point2& p)
    {
        if(this != &p)
        {
            x = p.x;
            y = p.y;
        }
        return *this;
    }

    /*@
        assigns \nothing;

        ensures \result == x;
    */
    int getX() const
    {
        return x;
    }

    /*@
        assigns \nothing;

        ensures \result == y;
    */
    int getY()const
    {
        return y;
    }

    /*@
        requires INT_MIN <= x + p.x <= INT_MAX;
        requires INT_MIN <= y + p.y <= INT_MAX;

        assigns x, y;

        ensures x == \old(x) + p.x;
        ensures y == \old(y) + p.y;

        ensures \result == *this;
    */
    Point2& operator +=(const Point2& p)
    {
        x += p.x;
        y += p.y;

        return *this;
    }

    /*@
        requires INT_MIN <= x - p.x <= INT_MAX;
        requires INT_MIN <= y - p.y <= INT_MAX;

        assigns x, y;

        ensures x == \old(x) - p.x;
        ensures y == \old(y) - p.y;

        ensures \result == *this;
    */
    Point2& operator -=(const Point2 p)
    {
        x -= p.x;
        y -= p.y;
        return *this;
    }

};



/*@
    assigns \nothing;

    ensures a == b; // logical equality
*/
inline
bool operator==(const Point2& a, const Point2& b)
{
    return a.getX() == b.getX() && a.getY() == b.getY();
}

/*@
    assigns \nothing;

    ensures !(a == b); // logical equality
    //ensures a.x != b.x || a.y != b.y;
*/
inline
bool operator !=(const Point2& a, const Point2& b)
{
    return !(a == b);
}

/*@
    requires INT_MIN <= a.x + b.x <= INT_MAX;
    requires INT_MIN <= a.y + b.y <= INT_MAX;

    assigns \nothing;

    ensures \result.x == a.x + b.x;
    ensures \result.y == a.y + b.y;
*/
inline
Point2 operator+(const Point2& a, const Point2& b)
{
    Point2 c(a);
    c += b;
    return c;
}


/*@
    requires INT_MIN <= a.x - b.x <= INT_MAX;
    requires INT_MIN <= a.y - b.y <= INT_MAX;

    assigns \nothing;

    ensures \result.x == a.x - b.x;
    ensures \result.y == a.y - b.y;
*/
inline
Point2 operator-(const Point2& a, const Point2& b)
{
    Point2 c(a);
    c -= b;
    return c;
}

