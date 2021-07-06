typedef unsigned short u16_t;

class A
{
public:

  bool is_zero() { return this->str.type == 0; }

  union {
    u16_t raw;
    struct {
      u16_t prec : 10;
      u16_t main : 5;
      u16_t type : 1;
    } str;
  };

  bool is_foo();

};

bool A::is_foo() { return (1 << str.main) == 0; }
