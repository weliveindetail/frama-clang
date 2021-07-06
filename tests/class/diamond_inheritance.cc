class ios_base
{ protected:
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
   char* getContent() const { return (char*) m_content; }
   void setContent(char* content) { m_content = (_CharT*) content; }
};


template<typename _CharT> class basic_istream : public virtual ios_base
{ public:
   explicit basic_istream() {}
   virtual ~basic_istream() {}

   void init(basic_stringbuf<_CharT>* buf)
     { m_buf = buf->getContent(); }
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

template<typename _CharT> class basic_ostream : public virtual ios_base
{ public:
   basic_ostream() {}
   virtual ~basic_ostream() {}

   void init(basic_stringbuf<_CharT>* buf)
     { buf->alloc_content();
       buf->setContent(m_buf); /* not really realistic, just to see */
     }
};


template<typename _CharT>
class basic_ostringstream : public basic_ostream<_CharT>
{ public:
    typedef _CharT 					char_type;
    typedef basic_stringbuf<_CharT> 	__stringbuf_type;
    typedef basic_ostream<char_type>	__ostream_type;

  private:
    __stringbuf_type	_M_stringbuf;

  public:
    explicit
    basic_ostringstream(ios_base::openmode __mode = ios_base::in)
    : __ostream_type(), _M_stringbuf(__mode)
    { this->init(&_M_stringbuf); }
};

template<typename _CharT> class basic_stream : public basic_istream<_CharT>, public basic_ostream<_CharT>
{ public:
   basic_stream() : basic_istream<_CharT>(), basic_ostream<_CharT>(), ios_base() {}
   virtual ~basic_stream() {}

   void init(basic_stringbuf<_CharT>* buf)
     { basic_istream<_CharT>::init(buf);
       basic_ostream<_CharT>::init(buf);
     }
};


template<typename _CharT>
class basic_stringstream : public basic_istringstream<_CharT>, public basic_ostringstream<_CharT>
{ public:
    typedef _CharT 					char_type;
    typedef basic_stringbuf<_CharT> 	__stringbuf_type;

  public:
    explicit
    basic_stringstream(ios_base::openmode __mode = ios_base::in)
    : basic_istringstream<_CharT>(__mode), basic_ostringstream<_CharT>(__mode)
    {}
};

int main()
{ basic_stream<char> a;
  basic_stringstream<char> b;
}
