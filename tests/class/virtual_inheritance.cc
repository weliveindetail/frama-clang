class ios_base
{ public:
   char* m_buf;

  public:
   enum openmode { in, out, inout };
   ios_base() : m_buf((char*) 0) {}
   ios_base(const ios_base& source);
   virtual ~ios_base();
};


template<typename _CharT> class basic_stringbuf
{ private:
   _CharT* m_content;

  public:
   basic_stringbuf(ios_base::openmode mode = ios_base::in)
     : m_content((char*) 0) {}
   void alloc_content();
};


template<typename _CharT> class basic_istream : public virtual ios_base
{ public:
   explicit basic_istream() {}
   virtual ~basic_istream() {}

   void init(basic_stringbuf<_CharT>* buf)
     { buf->alloc_content(); }
};


template<typename _CharT>
class basic_istringstream : public basic_istream<_CharT>
{ public:
    typedef _CharT 					char_type;
    typedef basic_stringbuf<_CharT> 	__stringbuf_type;
    typedef basic_istream<char_type>	__istream_type;

  private:
    __stringbuf_type	_M_stringbuf;

  public:
    explicit
    basic_istringstream(ios_base::openmode __mode = ios_base::in)
    : __istream_type(), _M_stringbuf(__mode)
    { this->init(&_M_stringbuf); }
};

int atoi(char* buf);

basic_istream<char>&
operator>>(basic_istream<char>& in, int& result) {
  result = atoi(in.m_buf);
  return in;
}

int main()
{ basic_istringstream<char> a;
  int x;
  a >> x;
  return x;
}
