
class Employee { protected: int salary; }; 

class Manager : public Employee {
	//@ assigns salary,xxx;
	void punish(void) { salary = 0; }
};

