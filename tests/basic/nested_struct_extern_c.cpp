extern "C" {
  typedef struct {
    struct s {
      int buf;
    } s;
  } p;

  p x;
}

int main() { return x.s.buf; }
