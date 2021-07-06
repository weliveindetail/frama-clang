  template<typename _Value>
    struct __numeric_traits_integer
    {
      // Only integers for initialization of member constant.
      static const _Value __min = 0;
      static const _Value __max = 0;

      // NB: these two also available in std::numeric_limits as compile
      // time constants, but <limits> is big and we avoid including it.
      static const bool _is_signed = true;
      static const int __digits = 10;
    };

  template<typename _Value>
    const _Value __numeric_traits_integer<_Value>::__min;

  template<typename _Value>
    const _Value __numeric_traits_integer<_Value>::__max;

  template<typename _Value>
    const bool __numeric_traits_integer<_Value>::_is_signed;

  template<typename _Value>
    const int __numeric_traits_integer<_Value>::__digits;


template class __numeric_traits_integer<int>;

int main() {
  int x = __numeric_traits_integer<int>::__min;
  bool b = __numeric_traits_integer<int>::_is_signed;
  int d = __numeric_traits_integer<int>::__digits;
}
