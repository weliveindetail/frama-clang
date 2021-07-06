
template<typename _T> struct traits {
	struct st { typedef _T tp; };
};

traits<int>::st::tp x;

