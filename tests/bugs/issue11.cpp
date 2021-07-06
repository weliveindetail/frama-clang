namespace a {
template <class> class b { template <class> friend class b; };
b<void> c;
a::b<char> d;
}

