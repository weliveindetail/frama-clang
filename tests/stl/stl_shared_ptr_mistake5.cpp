// see http://www.acodersjourney.com/2016/05/top-10-dumb-mistakes-avoid-c-11-smart-pointers/

// try frama-c-gui stl/stl_shared_ptr_mistake5.cpp -cxx-stdinc -c11 -eva -eva-no-alloc-returns-null -slevel 100

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

void mistake5()
{
  Aircraft* myAircraft5 = new Aircraft(5);

  if (myAircraft5){

    std::shared_ptr<Aircraft> pAircraft51(myAircraft5);

    std::shared_ptr<Aircraft> pAircraft52(myAircraft5);
  }
}

int main()
{
  mistake5();
  return 0;
}
