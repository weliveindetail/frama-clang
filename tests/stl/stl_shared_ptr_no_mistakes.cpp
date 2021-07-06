/* run.config
DONTRUN: issue in remove_exn transformer
*/
// see http://www.acodersjourney.com/2016/05/top-10-dumb-mistakes-avoid-c-11-smart-pointers/

// try frama-c-gui stl/stl_shared_ptr_no_mistakes.cpp -cxx-stdinc -c11 -eva -eva-no-alloc-returns-null -slevel 100

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

void no_mistake5()
{
  Aircraft* myAircraft5 = new Aircraft(5);

  if (myAircraft5){

    std::shared_ptr<Aircraft> pAircraft51(myAircraft5);

    std::shared_ptr<Aircraft> pAircraft52(pAircraft51); // replace myAircraft5 by pAircraft51
  }
}

void no_mistake6()
{
  std::shared_ptr<Aircraft> pAircraft6(new Aircraft(6));
  Aircraft* myAircraft6 = pAircraft6.get(); // returns the raw pointer
  // delete myAircraft6;  // myAircraft is gone
}

int no_mistake10()
{
  Aircraft* myAircraft5 = new Aircraft(5);

  if (myAircraft5){

    std::shared_ptr<Aircraft> pAircraft51(myAircraft5);

    std::shared_ptr<Aircraft> pAircraft52(pAircraft51);
  }

  std::shared_ptr<Aircraft> pAircraft100(new Aircraft(100));
  std::shared_ptr<Aircraft> pAircraft101(new Aircraft(101));

  pAircraft100->myWingMan = pAircraft101;
  pAircraft101->m_flyCount = 17;

  int res = pAircraft100->myWingMan.lock()->m_flyCount; // OK here

  pAircraft101.reset(); // destroy the object managed by pAircraft101

  return res;
}


int main()
{
  no_mistake5();
  no_mistake6();
  int res = no_mistake10();
  return res;
}
