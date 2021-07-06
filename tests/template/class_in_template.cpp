namespace std {
  class ios_base {
  public:
    static const int bad_bit = 1;
  };

  template<typename _CharT>
    class basic_ios;

  template<typename _CharT>
    class basic_ostream;

  typedef basic_ios<char> 		ios; 

  typedef basic_ostream<char> 		ostream;

} // namespace

namespace std {

  template<typename _CharT>
    inline void
    __ostream_write(basic_ostream<_CharT>& __out,
      const _CharT* __s, int __n)
    {
      typedef basic_ostream<_CharT> __ostream_type;
      typedef typename __ostream_type::ios_base __ios_base;
      __out.setstate(__ios_base::badbit);
    }

  template<typename _CharT>
    inline void
    __ostream_fill(basic_ostream<_CharT>& __out, int __n)
    {
      typedef basic_ostream<_CharT> __ostream_type;
      typedef typename __ostream_type::ios_base __ios_base;
      __out.setstate(__ios_base::badbit);
    }

  template<typename _CharT>
    basic_ostream<_CharT>&
    __ostream_insert(basic_ostream<_CharT>& __out,
       const _CharT* __s)
    {
      typedef basic_ostream<_CharT> __ostream_type;
      typedef typename __ostream_type::ios_base __ios_base;
      __out.setstate(__ios_base::badbit);
      return __out;
    }

  extern template ostream& __ostream_insert(ostream&, const char*);
}

namespace std {
  template<typename _CharT>
    inline basic_ostream<_CharT>&
    operator<<(basic_ostream<_CharT>& __os, const _CharT* __s)
    { return __ostream_insert(__os, __s);
    }

  extern template
    basic_ostream<char>&
    operator<<(basic_ostream<char>&, const char*);
}

namespace std {

    template<typename _CharT>
    class basic_ios : public ios_base
    {
    public:
      typedef _CharT char_type;

    protected:
      basic_ostream<_CharT>* _M_tie;

    public:
      basic_ios() : _M_tie(0) {}
      void setstate(int state) {}
    };

  template<typename _CharT>
    class basic_ostream : public basic_ios<_CharT>
    {
    public:
      class sentry;
      
    };

  template<typename _CharT>
    inline basic_ostream<_CharT>&
    operator<<(basic_ostream<_CharT>& __out, _CharT __c)
    { return __ostream_insert(__out, &__c); }

  template<typename _CharT>
  class basic_ostream<_CharT>::sentry {
    basic_ostream<_CharT>& _M_os;

   public:
    explicit sentry(basic_ostream<_CharT>& __os);
    ~sentry() {}
  };

  extern template class basic_ostream<char>;

}

int main() {
  std::ostream out;
  out << 'c';
  return 0;
}
