

struct node { node* nxt; };

node tmp;

//@ assigns tmp.nxt, *pos;
void insert(node *pos) {
	tmp.nxt = pos;
	*pos = tmp;
}

