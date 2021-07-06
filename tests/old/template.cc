#define FRAMA_C_MALLOC_INDIVIDUAL
// #include "cxx_builtin.cc"
// #include "malloc.cc"
#define NULL ((void*)0)

template <class T> class Liste;

template <class T>
class Noeud {
private:
  T* val;
  Liste<T>* next;
public:
  Noeud(T* _data=(T*)NULL, Liste<T>* _next=(Liste<T>*) NULL)//;
    {
    val = _data;
    if (_data) next = _next;
    else next = (Liste<T>*)NULL;
    return;
    };
  T* head() { return val; };
  Liste<T>* tail () { return next; };
  ~Noeud();
};

template <class T>
class Liste {
private:
  Noeud<T>* top;
public:
  Liste(Noeud<T>* _top=(Noeud<T>*) NULL){ top = _top; } ;
  Liste(const Liste<T>& l) { top = l.top; };
  bool isEmpty() { return (top == NULL); }
  void cons(T* data);
  void cdr ();
  T* head ();
  ~Liste() { if (top) delete top; return; };
};
template <class T> Noeud<T>::~Noeud() { if (next) delete next; return; }

template <class T>
void Liste<T>::cons (T* data) {
  if (!data) return;
  Liste<T>* l = new Liste(*this);
  Noeud<T>* hd = new Noeud<T>(data, l);
  top = hd;
}

template <class T>
Liste<T>* foo(Liste<T>* BAD=NULL) { return BAD; }


template <class T>
void Liste<T>::cdr () {
  if (!top) return;
  Liste<T>* next = top -> tail ();
  if (!next) top = NULL; else top = next -> top;
}

template <class T>
T* Liste<T>::head () {
  if (!top) return NULL;
  return (top -> head());
}

int main () {
  Liste<bool> lb;
  Liste<int> li;
  int x = 3;
  bool b = false;
  lb.cons (&b);
  li.cons(&x);
  return 0;
}
