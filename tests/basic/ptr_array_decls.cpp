struct S0 {
   int  f0;
   int  f1;
};
struct S0 g_146[2][1] = 
  {
    {
      {42,43}
    },
    {
      {44,45}
    }
  };

struct S0* foo[2][1] =
  {
    { &g_146[0][0] },
    { &g_146[1][0] }
  };

struct S0 (*bar)[2][1] = &g_146;

struct S0 arr[1] = { {36,37} };

struct S0 (*(bla[2]))[1] = { &arr, &arr };

struct S0 (*(*complex_declaration)[2])[1] = &bla;

int x = 0;
int * y = &x;
int * const * z = &y;
