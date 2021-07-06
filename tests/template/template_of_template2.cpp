template <typename>
struct c;

template <typename>
struct a { template <typename> friend struct c; };
template <typename>
struct b { template <typename> friend struct a; };
template <typename>
struct c { template <typename> friend struct b; };
c<void> x;
c<char> y;

