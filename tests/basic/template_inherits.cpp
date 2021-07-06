template <typename>
class A {
    void m_fn1();
};

class B : A<B>
{};

template <typename P>
void A<P>::m_fn1() {
    delete (P*)0;
}

template class A<B>;

