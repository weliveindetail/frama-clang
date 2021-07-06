#include <algorithm>
#include <array>
#include <iterator>
#include <functional>

std::array<int,5> a = { 0, 1, 2, 3, 4 };

std::array<int,2> search = { 2, 3 };

std::array<int,5> b = { 5, 6, 7, 8, 9 };

typedef std::array<int,5>::iterator array_it5;
typedef std::array<int,2>::iterator array_it2;

bool positive(int x) { return x > 0; };

void ignore(int x) { };

int main () {
 int res = 0;
 if (std::all_of<array_it5, decltype(positive)>(a.begin(), a.end(), positive))
   res++;
 if (std::any_of<array_it5, decltype(positive)>(a.begin(), a.end(), positive))
   res++;
 if (std::none_of<array_it5, bool(*)(int)>(a.begin(), a.end(), positive))
   res++;

   std::for_each<array_it5, decltype(&ignore)>(a.begin(), a.end(), ignore);

 if (std::find<array_it5, int>(a.begin(), a.end(), 3) != a.end()) res++;
 if (std::find_if<array_it5, decltype(positive)>(a.begin(), a.end(), positive)
     != a.end())
   res++;
 if (std::find_if_not<array_it5, decltype(positive)>
     (a.begin(), a.end(), positive)
     != a.end())
   res++;

 if (std::find_end<array_it5, array_it2>(
       a.begin(), a.end(), search.begin(), search.end())
     != a.end())
   res++;

 if (std::find_end<array_it5, array_it2, std::less<int>>(
       a.begin(), a.end(), search.begin(), search.end(),std::less<int>())
     != a.end())
   res++;

 if (std::find_first_of<array_it5, array_it2>(
       a.begin(), a.end(), search.begin(), search.end())
     != a.end())
   res++;

 if (std::find_first_of<array_it5, array_it2, std::less<int>>(
       a.begin(), a.end(), search.begin(), search.end(), std::less<int>())
     != a.end())
   res++;

 if (std::adjacent_find<array_it5>(a.begin(), a.end()) == a.end()) res++;

 if (std::adjacent_find<array_it5, std::less<int>>(
       a.begin(), a.end(), std::less<int>())
     != a.end())
   res++;

 if (std::count<array_it5, int>(a.begin(), a.end(), 3) == 1) res++;

 if (std::count_if<array_it5, decltype(positive)>(
       a.begin(), a.end(), positive)
     == 4)
   res++;

 { auto sb = search.begin();
   auto ab = a.begin();
   auto rm = std::mismatch<array_it2, array_it5>(sb, search.end(), ab);
   if (rm.first == sb && rm.second == ab) res++;
 }

 {
     auto sb = search.begin();
     auto ab = a.begin();
     auto rm = std::mismatch<array_it2, array_it5, std::less<int>>(
       search.begin(), search.end(), a.begin(), std::less<int>());
   if (rm.first == sb && rm.second == ab) res++;
 }

 if (std::equal<array_it5,array_it5>(a.begin(), a.end(), a.begin())) res++;

 if (std::equal<array_it5,array_it5,std::equal_to<int>>(
       a.begin(), a.end(), a.begin(), std::equal_to<int>()))
   res++;

 if (std::is_permutation<array_it5, array_it5>(a.begin(), a.end(), a.begin()))
   res++;

if (std::is_permutation<array_it5, array_it5, std::equal_to<int>>(
       a.begin(), a.end(), a.begin(), std::equal_to<int>()))
   res++;

 std::array<int,5> dest = { };
 std::copy<array_it5, array_it5>(a.begin(),a.end(),dest.begin());

 return res;
}
