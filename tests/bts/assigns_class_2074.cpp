struct Employee {
	int dept;
	//@ assigns dept;
	Employee(int d) : dept(d) {}
};



struct Manager : public Employee {
	//@ assigns Employee::dept;
	Manager(int d) : Employee(d) {}
};

