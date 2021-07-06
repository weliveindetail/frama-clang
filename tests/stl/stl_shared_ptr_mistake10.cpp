// see http://www.acodersjourney.com/2016/05/top-10-dumb-mistakes-avoid-c-11-smart-pointers/

// try frama-c-gui stl/stl_shared_ptr_mistake10.cpp -cxx-stdinc -c11 -eva -eva-no-alloc-returns-null -slevel 100

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

int mistake10()
{
  std::shared_ptr<Aircraft> pAircraft100(new Aircraft(100));
  std::shared_ptr<Aircraft> pAircraft101(new Aircraft(101));

  pAircraft100->myWingMan = pAircraft101;
  pAircraft101->m_flyCount = 17;

  pAircraft101.reset(); // destroy the object managed by pAircraft101

  int res = pAircraft100->myWingMan.lock()->m_flyCount; // ACCESS VIOLATION

  return res;
}


int main()
{
  int res = mistake10();
  return res;
}
