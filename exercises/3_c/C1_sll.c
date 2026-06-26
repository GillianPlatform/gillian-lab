// ========== Exercise C1: SLL ==========
//
// Welcome to the C exercises!
// Note that verifying C is more complex than WHILE, and thus Gillian's C
// implementation is a tad less robust than WISL; crashes and freezes may occur
// as you experiment.
//
// Unlike WHILE, we now need to worry about integer overflow. To reason about
// the size of integers, this Gillian implementation provides internal
// predicates to specify the bounds of a number, for bool, char, int, size_t and
// ssize_t; for example, use i__is_int(#x) to specify that #x can be represented
// as an int.
//
// Try verifying these SLL functions. We're in auto mode, and tactics are not
// necessary for verification. However, should you like to use some tactics to
// play around and understand what's going on, note that the syntax is a bit
// different; you must use __GILLIAN("tactic") instead of [[ tactic ]], like so:
//
// [[ fold p(x, y) ]]
//   -->  __GILLIAN("fold p(x, y)")
// [[ assert { bind: #c } (#c == #c + #b) ]]
//   -->  __GILLIAN("assert [[ bind #c ]] (#c == #a + #b)")

//#region  === DON'T EDIT THIS ===

#include <stdlib.h>

typedef struct ln {
    int data;
    struct ln *next;
} SLL;

/*@
pred sll(+p, alpha) {
  (p -m> struct ln { #head; #tail }) *
  (alpha == #head::#beta) *
  sll(#tail, #beta) *
  i__is_size_t(len alpha);

  (p == NULL) * (alpha == [])
}
*/

//#endregion  === EDIT BELOW HERE ===

/*@ spec listLength(x) {
  requires: sll(#x, #alpha) * (x == #x)
  ensures:  sll(#x, #alpha) * (ret == len #alpha)
} */
int listLength(SLL *x) {
    if (x == NULL) {
        return 0;
    } else {
        return 1 + listLength(x->next);
    };
}

/*@ spec listPrepend(x, v) {
  requires: (x == #x) * sll(#x, #alpha) * (v == #v)
  ensures: sll(ret, #v::#alpha)
} */
SLL* listPrepend(SLL *x, int v) {
  SLL *el = malloc(sizeof(SLL));
  el->data = v;
  el->next = x;
  return el;
}

/*@ spec listConcat(x, y) {
  requires: (x == #x) * (y == #y) * sll(#x, #alpha) * sll(#y, #beta)
  ensures:  sll(ret, #alpha @ #beta)
} */
SLL* listConcat(SLL *x, SLL *y) {
    SLL *r;
    if (x == NULL) {
        r = y;
    } else {
        SLL *c = listConcat(x->next, y);
        x->next = c;
        r = x;
    };
    return r;
}

