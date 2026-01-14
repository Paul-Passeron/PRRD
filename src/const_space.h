#ifndef CONST_SPACE_H
#define CONST_SPACE_H
#include "common.h"
#include "lst.h"

void back_again(lst_t bp, lst_t sp, lst_t np);
void tortoise_hare(lst_t bp, lst_t sp, lst_t fp, lst_t qp);
void value_reverse(lst_t sp, lst_t qp);

#ifdef CONST_SPACE_IMPL
#include "predicates.h"

//@ ghost list_shape ls;
//@ ghost int tortoise_hare_k;
//@ ghost int back_again_k;



/*@ requires qp == NULL || \exists int i; 0 <= i < ls.count ==>
 ls.cells[i] == qp;
  @ requires valid_list(sp);
  @ requires valid_list(qp);
  @ requires \forall integer i, j; 0 <= i < j <= ls.count ==> \separated(ls.cells[i], ls.cells[j]);
  @ requires ls.count < 10E5;
  @ requires \valid(ls.cells[0..ls.count]);
  @ requires listLR(ls, sp, (int)0, (int)ls.count,
 qp);
  @ requires \valid(ls.cells[0..ls.count]);
  @ assigns ls.cells[0..ls.count]->car \from(ls.cells[0..ls.count]->car);
  @ assigns ls.cells[0..ls.count]->cdr \from(ls.cells[0..ls.count]);
  @ ensures listLR(ls, sp, (int)0, (int)ls.count,
 qp);
  @ ensures \forall int i; 0 <= i < ls.count ==>
    ls.cells[i]->car ==
 \old(ls.cells[ls.count - 1 - i]->car) &&
    ls.cells[i]->cdr ==
 \old(ls.cells[ls.count - 1 - i]->cdr);
 @ ensures frame_list{Old, Post}(ls);
 */
void value_reverse(lst_t sp, lst_t qp) {

  //@ ghost tortoise_hare_k = 0;
  tortoise_hare(NULL, sp, sp, qp);
}

/*@ lemma separated_preserves_cdr{L1,L2}:
  \forall lst_t p, q;
    \separated(\at(p, L1), \at(q, L1)) &&
    \valid{L1}(\at(p, L1)) && \valid{L1}(\at(q, L1)) &&
    \valid{L2}(\at(p, L2)) && \valid{L2}(\at(q, L2))
    ==> \at(q->cdr, L1) == \at(q->cdr, L2);
*/

/*@ lemma two_separated_cons{L}:
  \forall lst_t nbp, bp, sp;
    valid_list{L}(nbp) &&
    valid_list{L}(bp) &&
    valid_list{L}(sp) &&
    \at(bp->cdr, L) == sp &&
    (\forall integer i; 0 <= i < length{L}(nbp) ==> \separated(nth{L}(nbp, i), bp)) &&
    two_separated{L}(nbp, sp)
    ==> two_separated{L}(nbp, bp);
*/


/*@ axiomatic LengthNthRelation {

  axiom length_null:
    length(\null) == 0;

  axiom length_cons:
    \forall lst_t l;
    l != \null ==>
    length(l) == 1 + length(l->cdr);

  lemma nth_length_base:
    \forall lst_t l;
    nth(l, 0) == \null ==>
    l == \null && length(l) == 0;

  lemma nth_length_inductive:
    \forall lst_t l, integer n;
    n >= 0 && l != \null && nth(l->cdr, n) == \null && length(l->cdr) == n ==>
    nth(l, n+1) == \null && length(l) == n + 1;

  // TODO: THIS IS PROBABLY SO BAD

  axiom nth_length_null:
    \forall lst_t l, integer n;
    n >= 0 && nth(l, n) == \null && valid_list(l) && (\forall integer i; 0 <= i < n ==> nth(l, i) != \null ) ==>
    length(l) == n;


    axiom valid_list_has_length:
        \forall lst_t l;
        valid_list(l) ==>
        \exists integer n; n >= 0 && nth(l, n) == \null && length(l) == n;
}


*/


/*@ lemma pos_len_means_nonnull:
    \forall lst_t l; valid_list(l) && length(l) > 0 ==> l != \null;
*/

/*@ lemma pos_len_means_valid:
    \forall lst_t l; valid_list(l) && length(l) > 0 ==> \valid(l);
*/

/*@ lemma sup_one_len_means_cdr_nonnull:
    \forall lst_t l; valid_list(l) && length(l) > 1 ==> l->cdr != \null;
*/

/*@ lemma sup_one_len_means_cdr_valid:
    \forall lst_t l; valid_list(l) && length(l) > 1 ==> \valid(l->cdr);
*/

/*@ lemma valid_lst_forall:
 \forall lst_t l; valid_list(l) && l != \null ==> valid_list(nth(l, 1));
 */

/*@ lemma length_is_always_positive:
  \forall lst_t l; valid_list(l) ==> length(l) >= 0;
*/

/*@ lemma length_rel_with_cdr_0:
 \forall lst_t l; valid_list(l) && l != \null ==> length(l) > 0;
*/

/*@ lemma length_rel_with_cdr_1:
 \forall lst_t l; valid_list(l) && l != \null ==> length(l) == length(l->cdr) + 1;
*/

/*@ lemma valid_nth_range_means_non_null:
    \forall lst_t l; valid_list(l) && l != \null ==> \forall integer i; 0 <= i < length(l) ==> nth(l, i) != \null;
*/

/*@ lemma valid_nonnull_lst_implies_separation:
 \forall lst_t l; valid_list(l) && l != \null ==> \forall integer i, j; 0 <= i < j < length(l) ==> \separated(nth(l, i), nth(l, j));
 */

 /*@ lemma listRL_nth_is_cells:
     \forall list_shape ls, lst_t p, integer k, i;
     listRL(ls, p, k) && 0 <= i < k ==>
     nth(p, i) == ls.cells[k - 1 - i];
 */

 /*@ lemma listLR_nth_is_cells:
     \forall list_shape ls, lst_t p, integer lo, hi, lst_t q, integer i;
     listLR(ls, p, lo, hi, q) && 0 <= i < hi - lo ==>
     nth(p, i) == ls.cells[lo + i];
 */

/*@ requires \valid(ls.cells[0..ls.count]);
  @ requires ((bp == NULL || sp == NULL) && back_again_k >= 0) || back_again_k > 0;
  @ requires \forall integer i, j; 0 <= i < j <= ls.count ==> \separated(ls.cells[i], ls.cells[j]);
  @ requires bp != NULL && sp != NULL ==> sp != bp;
  @ requires valid_list(sp);
  @ requires valid_list(bp);
  @ requires valid_list(np);
  @ requires two_separated(bp, sp);
  @ requires ls.count < 10E5;
  @ requires listLR(ls, sp, back_again_k, ls.count,
ls.cells[ls.count]);
  @ requires listRL(ls, bp, back_again_k);
  @ requires back_again_k <= ls.count - back_again_k;
  @ requires ls.cells[ls.count - back_again_k] == np;
  @ requires \valid(ls.cells[0..ls.count]);
  @ decreases back_again_k;
  @ assigns ls.cells[0..ls.count]->car \from(ls.cells[0..ls.count]->car);
  @ assigns ls.cells[0..ls.count]->cdr \from(ls.cells[0..ls.count]);
  @ ensures listLR(ls, ls.cells[0], (int)0,
(int)(ls.count), ls.cells[ls.count]);
  @ ensures reversal{Old, Post}(ls, (int)0);
  @ ensures frame_list{Old, Post}(ls);
  @ ensures back_again_k >= 0;
*/
void back_again(lst_t bp, lst_t sp, lst_t np) {

  if (bp == NULL || np == NULL)
    return;
  elt_t tmp = bp->car;
  //@ assert(two_separated(bp, sp));
  bp->car = np->car;
  //@ assert(two_separated(bp, sp));
  /*@ assert valid_list(bp); */
  np->car = tmp;
  //@ assert(two_separated(bp, sp));
  /*@ assert valid_list(np); */

  //@ assert valid_list(bp);
  //@ assert length(bp) == length(bp->cdr) + 1;
  //@ assert \forall integer i; 0 <= i < length(bp->cdr) ==> nth(bp->cdr, i) == nth(bp, i + 1);
  //@ assert \forall integer i; 0 <= i < length(bp->cdr) ==> nth(bp->cdr, i) != NULL;
  //@ assert valid_list(bp) && bp != \null;
  //@ assert \forall integer i; 0 <= i < length(bp) - 1 ==> \separated(bp, nth(bp, i + 1));

  //@ assert \forall integer i; 0 < i < length(bp) ==> \separated(bp, nth(bp, i));

  lst_t nbp = bp->cdr;

  //@ assert back_again_k > 0;
  //@ assert back_again_k >= 1;

  //@ assert \forall integer i; 0 < i < length(bp) ==> \separated(bp, nth(bp, i));

  //@ assert bp == ls.cells[back_again_k - 1];

  //@ assert back_again_k - 1 > 0 ==> ls.cells[back_again_k - 1]->cdr == ls.cells[back_again_k - 2];
  //@ assert back_again_k - 1 > 0 ==> bp->cdr == ls.cells[back_again_k - 2];
  //@ assert back_again_k - 1 > 0 ==> nbp == ls.cells[back_again_k - 2];

  //@ assert back_again_k - 1 < back_again_k;
  //@ assert back_again_k - 2 < back_again_k - 1;

  //@ assert \forall integer i; back_again_k <= i <= ls.count ==> back_again_k - 2 < i;
  //@ assert \forall integer i; back_again_k <= i <= ls.count ==> back_again_k - 2 != i;
  //@ assert \forall integer i; back_again_k <= i <= ls.count ==> \separated(ls.cells[back_again_k - 2], ls.cells[i]);
  //@ assert \forall integer i; back_again_k <= i <= ls.count ==> nbp == ls.cells[back_again_k - 2] ==> \separated(nbp, ls.cells[i]);

  //@ assert bp == ls.cells[back_again_k - 1];
  //@ assert back_again_k - 1 < back_again_k;
  //@ assert \forall integer i; back_again_k <= i <= ls.count ==> back_again_k - 1 < i;
  //@ assert \forall integer i; back_again_k <= i <= ls.count ==> back_again_k - 1 != i;

  // Utiliser la séparation pour déduire l'inégalité des pointeurs
  //@ assert \forall integer i; back_again_k <= i <= ls.count ==> \separated(ls.cells[back_again_k - 1], ls.cells[i]);
  //@ assert \forall integer i; back_again_k <= i <= ls.count ==> ls.cells[back_again_k - 1] != ls.cells[i];
  //@ assert \forall integer i; back_again_k <= i <= ls.count ==> bp != ls.cells[i];
  //@ assert \forall integer i; back_again_k <= i <= ls.count ==> \separated(nbp, ls.cells[i]);
  //@ assert \forall integer i; back_again_k <= i < ls.count ==> \separated(nbp, ls.cells[i+1]);

  //@ assert sp == ls.cells[back_again_k];
  //@ assert two_separated(nbp, sp);
  bp->cdr = sp;
  //@ assert bp == ls.cells[back_again_k - 1];

  //@ assert \forall integer i; back_again_k <= i <= ls.count ==> back_again_k - 1 < i;

  //@ assert \forall integer i; back_again_k <= i <= ls.count ==> \separated(ls.cells[back_again_k - 1], ls.cells[i]);
  //@ assert \forall integer i; back_again_k <= i <= ls.count ==> \separated(bp, ls.cells[i]);
  //@ assert \forall integer i; back_again_k <= i <= ls.count ==> bp != ls.cells[i];

  //@ assert \forall integer i; back_again_k <= i < ls.count ==> ls.cells[i]->cdr == ls.cells[i+1];

  //@ assert listLR(ls, sp, back_again_k, ls.count, ls.cells[ls.count]);

  //@ assert bp->cdr == sp;
  //@ assert bp == ls.cells[back_again_k - 1];
  //@ assert sp == ls.cells[back_again_k];

  //@ assert listLR(ls, sp, back_again_k, ls.count, ls.cells[ls.count]);

  //@ assert nbp != NULL;
  //@ assert back_again_k - 1 > 0;
  //@ assert nbp == ls.cells[back_again_k - 2];
  //@ assert ls.cells[0]->cdr == NULL;
  //@ assert \forall integer i; 0 < i < back_again_k - 1 ==> ls.cells[i]->cdr == ls.cells[i - 1];
  //@ assert listRL(ls, nbp, back_again_k - 1);

  //@ assert \forall integer i; back_again_k <= i < ls.count ==> \separated(nbp, ls.cells[i+1]);

  //@ assert \forall integer i; 0 <= i < length(nbp) ==> \separated(bp, nth(nbp, i));

  //@ assert valid_list(nbp);
  //@ assert valid_list(sp);
  //@ assert valid_list(bp);
  //@ assert two_separated(nbp, bp);
  //@ ghost back_again_k = back_again_k - 1;

  back_again(nbp, bp, np->cdr);
}

/*@lemma all_sep_means_index_eq_means_eq:
  \forall lst_t *tab, integer i, j; \exists integer n; n >= 0 && \valid(tab[(0..n)]) &&
  (\forall integer n1, n2; 0 <= n1 < n2 <= n ==> \separated(tab[n1], tab[n2])) &&
  0 <= i <= n && 0 <= j <= n ==> (tab[i] == tab[j] ==> i == j);
*/

/*@ requires fp == NULL ==> qp == NULL;
  @ requires bp != NULL && sp != NULL ==> sp != bp;
  @ requires tortoise_hare_k >= 0;
  @ requires \forall integer i, j; 0 <= i < j <= ls.count ==> \separated(ls.cells[i], ls.cells[j]);
  @ requires valid_list(bp);
  @ requires valid_list(sp);
  @ requires valid_list(fp);
  @ requires valid_list(qp);
  @ requires two_separated(bp, sp);
  @ requires ls.count < 10E5;
  @ requires ls.count >= 0;
  @ requires \valid(ls.cells[0..ls.count]);
  @ requires listLR(ls, sp, tortoise_hare_k,
  ls.count, qp);
  @ requires listRL(ls, bp, tortoise_hare_k);
  @ requires 2 * tortoise_hare_k <= ls.count;
  @ requires ls.cells[2*tortoise_hare_k] == fp;
  @ decreases ls.count - tortoise_hare_k;
  @ assigns ls.cells[0..ls.count]->car \from(ls.cells[0..ls.count]->car);
  @ assigns ls.cells[0..ls.count]->cdr \from(ls.cells[0..ls.count]);
  @ ensures listLR(ls, ls.cells[0], (int)0,
  ls.count, qp);
  @ ensures reversal{Old, Post}(ls, (int)0);
  @ ensures frame_list{Old, Post}(ls);
  @ ensures ls.count >= 0;
  @ ensures tortoise_hare_k >= 0;
 */

void tortoise_hare(lst_t bp, lst_t sp, lst_t fp, lst_t qp) {
  lst_t nfp;
  if (fp == qp) {
    //@ ghost back_again_k = tortoise_hare_k;
    //@ assert fp == ls.cells[2 * back_again_k];
    //@ assert qp == ls.cells[2 * back_again_k];
    //@ assert qp == ls.cells[ls.count];
    //@ assert 2 * back_again_k == ls.count;
    back_again(bp, sp, sp);
  } else if (sp && fp && (nfp = fp->cdr) && nfp == qp) {
    //@ ghost back_again_k = tortoise_hare_k;
    //@ assert fp == ls.cells[2 * back_again_k];
    //@ assert fp->cdr == qp;
    //@ assert fp->cdr == ls.cells[2 * back_again_k + 1];
    //@ assert qp == ls.cells[2 * back_again_k + 1];
    //@ assert 2 * back_again_k + 1 == ls.count;
    back_again(bp, sp, sp->cdr);
  } else {
    //@ assert valid_list(nfp);
    //@ assert nfp->cdr != \null;
    //@ assert valid_list(nfp->cdr);
    nfp = fp->cdr->cdr;
    //@ assert valid_list(nfp);
    lst_t nsp = sp->cdr;
    //@ assert valid_list(nsp);
    //@ assert valid_list(bp);
    sp->cdr = bp;
    //@ assert valid_list(sp->cdr);
    //@ assert valid_list(sp);

    //@ ghost tortoise_hare_k = tortoise_hare_k + 1;
    tortoise_hare(sp, nsp, nfp, qp);
  }
}

#endif // CONST_SPACE_IMPL
#endif // CONST_SPACE_H

#include <stdlib.h>
