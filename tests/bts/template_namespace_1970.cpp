
namespace std {
	template<typename> class allocator;

	template<typename _Tp, typename _Alloc = std::allocator<_Tp> >
	class vector { }; 
}

std::vector<int*> v;

