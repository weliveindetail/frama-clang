namespace a {
template <class> class b {
  template <class> friend class b;
public: int x;
};
b<void> c;
a::b<char>;
a::b<int> d;
class e;
a::b<e> f;
}
