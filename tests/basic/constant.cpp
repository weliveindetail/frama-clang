template<int n> int f() { return n; }
enum E {
  A = 2,
  B=3+4,
};

int main()
{
        switch (3) {
          case 1 + 2: return f<1 + 2>(); break;
          case A+B: 
          default: return 0;
        }
}
