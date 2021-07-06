struct C
{
  union {
	struct {
          int rcv_timeout;
          int snd_timeout;
        } __attribute__((packed)) x;
    unsigned int raw;
  };
};

struct C c;

int G[sizeof(C)];

int main() {
  struct C cc;
  return cc.raw;
}
