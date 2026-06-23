// ========== Exercise C3: DLL ==========
//
// Try your hand at these doubly-linked-list functions. Some you must implement,
// others you must add tactics to prove.
//
// ---------- STRETCH GOAL ----------
// You might notice that the DLL predicate doesn't actually reason about the
// `prev' pointer, and our program is thus under-specified. If you feel like
// *really* pushing yourself, try specifying it properly!
// This will be extremely hard (we haven't done it for this program yet),
// and you may come up against some bugs in this Gillian implementation -
// if so, let us know! You may want to refer to the dlsegl / dlsegr predicates
// in WISL exercise B.

//#region  === DON'T EDIT THIS ===

#include <stdlib.h>

typedef struct dln {
    int data;
    struct dln *prev;
    struct dln *next;
} DLL;

/*@
pred DLL(+x, alpha) {
  (x == NULL) * (alpha == nil);

  (x -m> struct dln {#val; #prev; #next}) *
  DLL(#next, #beta) *
  (alpha == #val :: #beta) *
  (not (#next == NULL)) *
  i__is_size_t(len alpha);

  (x -m> struct dln {#val; #prev; NULL}) *
  (alpha == [ #val ])
}
*/

DLL* listConcat(DLL *x, DLL *y);
DLL* listPrepend(DLL *x, int v);

//#endregion  === EDIT BELOW HERE ===

/*@ spec makeNode(x) {
  requires: (#x == x)
  ensures:  DLL(ret, [#x])
} */
DLL* makeNode(int x) {
    // Implement me!
    return NULL;
}

/*@ spec listAppend(x, v) {
  requires: (x == #x) * (v == #v) * DLL(#x, #alpha) * i__is_size_t(1 + len #alpha)
  ensures:  DLL(ret, #alpha @ [ #v ])
} */
DLL *listAppend(DLL *x, int v) {
    // Implement me!
    return NULL;
}

/*@ spec listCopy(x) {
  requires: (x == #x) * DLL(#x, #alpha)
  ensures:  DLL(#x, #alpha) * DLL(ret, #alpha)
} */
DLL* listCopy(DLL *x) {
    // Implement me!
    return NULL;
}

/*@ spec listPrepend(x, v) {
  requires: (x == #x) * (v == #v) * DLL(#x, #alpha) * i__is_size_t(1 + len #alpha)
  ensures:  DLL(ret, #v :: #alpha)
} */
DLL* listPrepend(DLL *x, int v) {
    DLL *node_v = makeNode(v);
    if (x == NULL) {
        return node_v;
    } else {
        x->prev = node_v;
        node_v->next = x;
        return node_v;
    };
}

/*@ spec listConcat(x, y) {
  requires: (x == #x) * (y == #y) * DLL(#x, #alpha) * DLL(#y, #beta) *
            i__is_size_t((len #alpha) + (len #beta))
  ensures:  DLL(ret, #alpha @ #beta)
} */
DLL* listConcat(DLL *x, DLL *y) {
    if (y == NULL) {
        return x;
    } else {
        if (x == NULL) {
            return y;
        } else {
            if (x->next == NULL) {
                x->next = y;
                y->prev = x;
                return x;
            } else {
                DLL *new_tail = listConcat(x->next, y);
                x->next = new_tail;
                return x;
            }
        }
    }
}

