// see http://www.acodersjourney.com/2016/05/top-10-dumb-mistakes-avoid-c-11-smart-pointers/

// try frama-c-gui stl/stl_shared_ptr_mistake6.cpp -cxx-stdinc -c11 -eva -eva-no-alloc-returns-null -slevel 100

#include <memory>
#include <stdlib.h>

class Aircraft
{
private:
  int m_id;

public:
  int m_flyCount;
  std::weak_ptr<Aircraft> myWingMan;

  void Fly()
  {
  }

  Aircraft(int id)
  {
    m_id = id;
  }

  Aircraft()
  {
    m_id = 0;
  }

  ~Aircraft()
  {
  }
  
};

void mistake6()
{
  std::shared_ptr<Aircraft> pAircraft6(new Aircraft(6));
  Aircraft* myAircraft6 = pAircraft6.get(); // returns the raw pointer
  delete myAircraft6;  // myAircraft is gone
}

int main()
{
  mistake6();
  return 0;
}
