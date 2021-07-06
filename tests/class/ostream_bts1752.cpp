
class ostream {
public: 
	ostream operator<<(const char*);
};

ostream cout;

int main() {
	cout<<"bar"<<"foo";
}

