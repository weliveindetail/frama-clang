typedef unsigned short u16_t;
class A
{
public:

    static A nil()
	{
	    A ret;
	    ret.raw = 0;
	    return ret;
	}
    static A one()
	{
	    A ret;
            ret.str.prec = 0;
	    ret.str.main = 1;
	    ret.str.type = 0;
	    return ret;
	}

    void set_raw(u16_t raw) { this->raw = raw; }

  bool is_zero() { return this->str.type == 0; }

  union {
    u16_t raw;
    struct {
      u16_t prec : 10;
      u16_t main : 5;
      u16_t type : 1;
    } str;

  };

  /*@logic u16_t foo() reads str.prec ; */

};

int main () {
  A a = A::one();
  a.str.type = 1;
  return 0;
}
