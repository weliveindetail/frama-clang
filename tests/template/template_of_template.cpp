namespace a {
template <typename> class b;
template <typename> class c;
}
namespace boost {
template <class> class e { template <class> friend class e;
 };
boost::e<void> d;
boost::e<a::c<a::b<char>>> x;
}
