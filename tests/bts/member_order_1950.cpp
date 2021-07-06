
class A
{
private:

    static int count;

public:

    /*@
        assigns count;
    */
    A()
    {
        count++;
    }

};


class B
{
public:

    /*@
        assigns count;
    */
    B()
    {
        count++;
    }

private:

    static int count;
};

