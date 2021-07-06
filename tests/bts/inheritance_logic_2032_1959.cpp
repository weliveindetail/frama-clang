// example from bug 2032, most likely similar to 1959
class Employee {
	int salary;
public:
	//@ assigns salary; ensures salary == s;
	Employee(int s) : salary(s) {}
};

class Manager : public Employee {
	int level;
public:
	//@ assigns salary, level; ensures salary == s; ensures level == l;
	Manager(int s, int l) : Employee(s), level(l) {}
};

