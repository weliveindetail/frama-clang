class ArrayFieldTest
{
private:
  int (* m_field)[256];

public:
  ArrayFieldTest ()
    { m_field = new int[4][256]; }
  ~ArrayFieldTest ()
    { delete [] m_field; }
};


