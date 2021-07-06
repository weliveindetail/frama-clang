
class string {
  char c;
public:
	string();
	string(const char*);
	string cat(string);
};

int main() {
	string s;
	s.cat("foo");
}

