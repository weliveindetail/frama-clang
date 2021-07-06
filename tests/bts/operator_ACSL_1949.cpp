
enum _e { _e0, _e1, _e2 };

//@ predicate operator==(int a,enum _e b) =      ( a - b <= 1 );
bool          operator==(int a,enum _e b) { return a - b <= 1; }


