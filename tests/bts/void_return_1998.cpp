
void g(int p) { }

void h(int p) { return g(p); }

template<typename Tp> Tp i(int p) { }

template<typename Tp> Tp j(int p) { return i<Tp>(p); }

int main(void) { j<void>(3); }
