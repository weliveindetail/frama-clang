int f(int);

class A{
public:
    int t3() const
    {
        int x = 0;
        x += (({for(int i=0;i<5;++i) x+=id(i);}),42);
        return x;
    }
    int id(int) const;
private:
    int _; // Non empty class
};

int A::id(int x) const {return x;}

int t1()
{
    int x = 0;
    x += 
    (
        ({
            /*@ loop invariant i>=0; */
            for(int i=0;i<5;++i)
                x+=f(i);
        }),
        42);
    return x;
}

int f(int x) { return x; }

int t2()
{
    int x = 0;
    x += (({for(int i=0;i<5;++i) x+=i;}),42);
    return x;
}

int main()
{
    A a;
    int x=t1();
    int y=t2();
    int z=a.t3();
    return x + 100*y + 10000*z;
}
