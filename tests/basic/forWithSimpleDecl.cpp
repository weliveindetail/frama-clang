struct s{float a;};
extern "C" int f(void);
int main()
{
    for (int p, e;;)
        ;
        
    for (int p, e;;)
        p=e;
        
    for(int i;;)
    {
        i = 17;
        break;
    }
    
    for(int p=3, e=p+1; ; )
        p+=e;

   for (int a; 1; (void)(a > f()))
    continue;
       
    double t[15];
    struct s i;
    float j;
    for(double i=0, *j=t, k;i<15;++i,++j,k--);
    j=i.a;
    return 0;
}

