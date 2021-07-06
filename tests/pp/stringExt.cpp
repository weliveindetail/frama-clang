int __fc_heap_status;

/*@
axiomatic StrLen {
  logic ℤ strlen{L}(char *s)
    reads *(s + (0 ..));
}
*/


/*@

predicate valid_string{L}(char *s) =
  0 <= strlen(s) && \valid(s + (0 .. strlen(s)));
  //0 ≤ strlen(s) ∧ \valid(s + (0 .. strlen(s)));

 */

/*@ axiomatic StrCmp {
  @ logic ℤ strcmp{L}(char *s1, char *s2)
  @   reads s1[0..strlen(s1)], s2[0..strlen(s2)];
  @
  @ axiom strcmp_zero{L}:
  @   \forall char *s1, *s2;
  @      strcmp(s1,s2) == 0 <==>
  @        (strlen(s1) == strlen(s2)
  @         && \forall ℤ i; 0 <= i <= strlen(s1) ==> s1[i] == s2[i]);
  @ }
  @*/



/*@
axiomatic dynamic_allocation {
  predicate is_allocable{L}(ℤ n)
    reads __fc_heap_status;

  axiom never_allocable{L}:
    \forall ℤ i; i < 0 || i > 4294967295U ==> !is_allocable(i);
    // ∀ ℤ i; i < 0 ∨ i > 4294967295U ⇒ ¬is_allocable(i);

  }
 */



// Allocate strings

/*@ allocates \result;
  @ assigns \result \from indirect:s[0..strlen(s)], indirect:__fc_heap_status;
  @ behavior allocation:
  @   assumes can_allocate: is_allocable(strlen(s));
  @   assigns __fc_heap_status \from indirect:s, __fc_heap_status;
  @   assigns \result \from indirect:s[0..strlen(s)], indirect:__fc_heap_status;
  @   ensures allocation: \fresh(\result,strlen(s));
  @   ensures result_valid_string_and_same_contents:
  @     valid_string(\result) && strcmp(\result,s) == 0;
  @ behavior no_allocation:
  @   assumes cannot_allocate: !is_allocable(strlen(s));
  @   assigns \result \from \nothing;
  @   allocates \nothing;
  @   ensures result_null: \result == \null;
  @*/
extern char *strdup (const char *s);

