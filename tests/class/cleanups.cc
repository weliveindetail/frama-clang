char* strdup(const char*);

class StringRepository {
  private:
   char* m_support;
   int m_shared;

  public:
   StringRepository(char* support) : m_support(support), m_shared(0) {}

   void incShared() { ++m_shared; }
   bool decShared() { --m_shared; return m_shared <= 0; }
};

class String {
  private:
   StringRepository* m_repository;

  public :
   String(const char* support)
     : m_repository(new StringRepository(strdup(support)))
     { m_repository->incShared(); }
   String(const String& source)
     : m_repository(source.m_repository)
     { m_repository->incShared(); }
   ~String()
     { if (m_repository->decShared()) delete m_repository; }
};

bool print(const String& source);

int main() {
  print("test1");
  print("test2");

  bool x = print("x") + print("y");

  if (print("condition"))
    print("yes");

  if (print("z") + print("t"))
    print("yes2");

  return print("return");
}

