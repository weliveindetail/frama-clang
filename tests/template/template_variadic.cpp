
template<typename...> struct Tuple {};

template<typename T1, typename T2> struct Pair {};

template<class ... Args1> struct zip {

  template<class ... Args2> struct with {
    typedef Tuple<Pair<Args1, Args2> ... > type;
  };
};

int main () {
  zip<int, signed char>::with<unsigned int, unsigned char>::type x;
}
