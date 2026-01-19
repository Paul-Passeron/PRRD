#ifndef CONST_SPACE_H
#define CONST_SPACE_H
#include "common.h"
#include "predicates.h"
#include "lst.h"


/*@ predicate valid_ls(list_shape ls) =
    ls.count >= 0 &&
    (\forall integer i; 0 <= i < ls.count ==> \valid(ls.cells[i]) && valid_list(ls.cells[i])) &&
    (\forall integer i; 0 <= i <= ls.count ==> valid_list(ls.cells[i])) &&
    (\forall integer i, j; 0 <= i < j <= ls.count ==> \separated(ls.cells[i], ls.cells[j])) &&
    (\forall integer i; 0 <= i <= ls.count ==>
        \forall integer j; 0 <= j < length(ls.cells[i]) ==>
            (\exists integer n; ls.cells[n] == nth(ls.cells[i], j))
    ) &&
    \valid(&ls.cells[0..ls.count]);
*/

/*@ predicate in_ls(list_shape ls, lst_t l) =
    valid_ls(ls) &&
    valid_list(l) &&
    \exists integer i; 0 <= i <= ls.count ==>
        l == ls.cells[i];
*/

 /*@ lemma listLR_length{L}:
     \forall list_shape ls, lst_t p, integer lo, hi, lst_t q;
     \at(valid_ls(ls), L) &&
     listLR{L}(ls, p, lo, hi, q)
     ==> length{L}(p) >= hi - lo;
 */

/*@ lemma in_ls_not_end_means_valid_aux:
    \forall list_shape ls, lst_t l; valid_ls(ls) && valid_list(l) && in_ls(ls, l) && \exists integer i; 0 <= i < ls.count ==> \valid(l) && valid_list(l);
*/

/*@ lemma in_ls_not_end_means_valid:
    \forall list_shape ls, lst_t l; valid_ls(ls) && valid_list(l) && in_ls(ls, l) && l != ls.cells[ls.count] ==> \valid(l) && valid_list(l);
*/

/*@ lemma valid_ls_means_all_sep_from_cdr:
    \forall list_shape ls; valid_ls(ls) ==> \forall integer i; 0 <= i < ls.count ==> ls.cells[i]->cdr == \null || \separated(ls.cells[i], ls.cells[i]->cdr);
*/

/*@ lemma all_sep_means_index_eq_means_eq:
 \forall list_shape ls, lst_t a, b; valid_ls(ls) &&
 in_ls(ls, a) &&
 in_ls(ls, b) ==>
 (\exists integer na, nb; 0 <= na < ls.count && 0 <= nb < ls.count ==> (a == ls.cells[na] && b == ls.cells[nb])
 ==> (a == b ==> na == nb));
*/

/*@ lemma all_nth_are_valid_if_not_end:
\forall list_shape ls, lst_t l; valid_ls(ls) && in_ls(ls, l) && \exists integer n; 0 <= n < ls.count ==> \forall integer i; 1 <= i < length(l) ==> \valid(nth(l, i)) && in_ls(ls, nth(l, i));
*/

/*@ lemma frame_cdr_other_cells{L1, L2}:
    \forall list_shape ls, integer idx;
    \at(valid_ls(ls), L1) &&
    0 <= idx < \at(ls.count, L1) &&
    (\forall integer j; 0 <= j < \at(ls.count, L1) && j != idx ==>
        \at(ls.cells[j]->cdr, L1) == \at(ls.cells[j]->cdr, L2))
    ==> \forall integer j; 0 <= j < \at(ls.count, L1) && j != idx ==>
        \at(ls.cells[j]->cdr, L1) == \at(ls.cells[j]->cdr, L2);
*/

/*@ lemma separated_cdr_frame{L1, L2}:
    \forall lst_t p, q;
    \separated(p, q) ==>
    \at(q->cdr, L1) == \at(q->cdr, L2);
*/

/*@ requires ((bp == \null || sp == \null) && k >= 0) || k > 0;
  @ requires bp != \null && sp != \null ==> sp != bp;
  @ requires valid_ls(ls);
  @ requires in_ls(ls, sp);
  @ requires in_ls(ls, bp);
  @ requires in_ls(ls, np);
  @ requires listLR(ls, sp, k, ls.count, ls.cells[ls.count]);
  @ requires listRL(ls, bp, k);
  @ requires k <= ls.count - k;
  @ requires ls.cells[ls.count - k] == np;
  @ decreases k;
  @ assigns ls.cells[0..ls.count]->car \from(ls.cells[0..ls.count]->car);
  @ assigns ls.cells[0..ls.count]->cdr \from(ls.cells[0..ls.count]);
  @ ensures listLR(ls, ls.cells[0], (int)0, (int)(ls.count), ls.cells[ls.count]);
  @ ensures reversal{Old, Post}(ls, (int)0);
  @ ensures ls.cells[ls.count] == \old(ls.cells[ls.count]);
*/
void back_again(lst_t bp, lst_t sp, lst_t np)
/*@ ghost (list_shape ls, int k) */
;

/*@ requires fp == \null ==> qp == \null;
  @ requires bp != \null && sp != \null ==> sp != bp;
  @ requires k >= 0;
  @ requires valid_ls(ls);
  @ requires in_ls(ls, bp);
  @ requires in_ls(ls, sp);
  @ requires in_ls(ls, fp);
  @ requires in_ls(ls, qp);
  @ requires qp == ls.cells[ls.count];
  @ requires ls.cells[2 * k] == fp;
  @ requires listLR(ls, sp, k, ls.count, qp);
  @ requires listRL(ls, bp, k);
  @ requires 2 * k <= ls.count;
  @ decreases ls.count - k;
  @ assigns ls.cells[0..ls.count]->car \from(ls.cells[0..ls.count]->car);
  @ assigns ls.cells[0..ls.count]->cdr \from(ls.cells[0..ls.count]);
  @ ensures listLR(ls, ls.cells[0], (int)0, ls.count, qp);
  @ ensures reversal{Old, Post}(ls, (int)0);
*/
void tortoise_hare(lst_t bp, lst_t sp, lst_t fp, lst_t qp)
/*@ ghost (list_shape ls, int k) */
;

/*@ requires qp == NULL || \exists int i; 0 <= i < ls.count ==> ls.cells[i] == qp;
  @ requires valid_ls(ls);
  @ requires valid_list(sp);
  @ requires valid_list(qp);
  @ requires listLR(ls, sp, (int)0, (int)ls.count, qp);
  @ assigns ls.cells[0..ls.count]->car \from(ls.cells[0..ls.count]->car);
  @ assigns ls.cells[0..ls.count]->cdr \from(ls.cells[0..ls.count]);
  @ ensures listLR(ls, sp, (int)0, (int)ls.count, qp);
  @ ensures \forall int i; 0 <= i < ls.count ==> ls.cells[i]->car == \old(ls.cells[ls.count - 1 - i]->car) && ls.cells[i]->cdr == \old(ls.cells[i]->cdr);
*/
void value_reverse(lst_t sp, lst_t qp)
/*@ ghost (list_shape ls) */;

#ifdef CONST_SPACE_IMPL

void value_reverse(lst_t sp, lst_t qp)
    /*@ ghost (list_shape ls) */
{
    //@ assert qp == ls.cells[ls.count];
    //@ assert listLR(ls, sp, (int)0, (int)ls.count, qp);
    //@ assert sp == ls.cells[0];
    //@ ghost lst_t old_qp = qp;
    tortoise_hare(NULL, sp, sp, qp) /*@ ghost (ls, 0) */;
    //@ assert listLR(ls, ls.cells[0], (int)0, (int)(ls.count), ls.cells[ls.count]);
    //@ assert qp == old_qp;  // qp variable unchanged
    //@ assert ls.cells[ls.count] == qp;
    //@ assert listLR(ls, ls.cells[0], (int)0, ls.count, qp);
}


void back_again(lst_t bp, lst_t sp, lst_t np)
/*@ ghost (list_shape ls, int k) */
{
    if (bp == NULL || np == NULL)
        return;
    elt_t tmp = bp->car;
    bp->car = np->car;
    np->car = tmp;
    lst_t nbp = bp->cdr;
    //@ assert listRL(ls, bp, k);
    //@ assert k > 0;
    //@ assert bp == ls.cells[k - 1];
    //@ assert listLR(ls, sp, k, ls.count, ls.cells[ls.count]);
    //@ assert sp == ls.cells[k];
    //@ assert \forall integer i; k <= i < ls.count ==> ls.cells[i]->cdr == ls.cells[i + 1];
    //@ assert k == 1 ==> nbp == \null;
    //@ assert k > 1 ==> nbp == ls.cells[k - 2];
    //@ assert ls.cells[0]->cdr == \null;
    //@ assert \forall integer i; 0 < i < k ==> ls.cells[i]->cdr == ls.cells[i - 1];
    //@ assert \forall integer i; 0 <= i < k - 1 ==> \separated(ls.cells[k-1], ls.cells[i]);
    bp->cdr = sp;
    //@ assert bp == ls.cells[k - 1];
    //@ assert \forall integer i; k <= i <= ls.count ==> \separated(ls.cells[k-1], ls.cells[i]);
    //@ assert \forall integer i; k <= i < ls.count ==> ls.cells[i]->cdr == ls.cells[i + 1];
    //@ assert ls.cells[k - 1]->cdr == ls.cells[k];
    //@ assert ls.cells[k - 1]->cdr == ls.cells[(k - 1) + 1];
    //@ assert \forall integer i; k - 1 <= i < ls.count ==> ls.cells[i]->cdr == ls.cells[i + 1];
    //@ assert listLR(ls, bp, (int)(k - 1), ls.count, ls.cells[ls.count]);
    //@ assert k == 1 ==> listRL(ls, nbp, (int)(k - 1));
    //@ assert k > 1 ==> ls.cells[0]->cdr == \null;
    //@ assert k > 1 ==> \forall integer i; 0 < i < k - 1 ==> ls.cells[i]->cdr == ls.cells[i - 1];
    //@ assert k > 1 ==> nbp == ls.cells[k - 2];
    back_again(nbp, bp, np->cdr) /*@ ghost (ls, k-1) */;
}

void tortoise_hare(
    lst_t bp,
    lst_t sp,
    lst_t fp,
    lst_t qp
)
/*@ ghost (list_shape ls, int k) */
{
    lst_t nfp;
    if (fp == qp) {
        back_again(bp, sp, sp) /*@ ghost(ls, k) */;
    } else {
        nfp = fp->cdr;
        if (sp && fp && nfp == qp) {
            //@ assert qp == ls.cells[ls.count];
            back_again(bp, sp, sp->cdr) /*@ ghost (ls, k) */;
            //@ assert listLR(ls, ls.cells[0], (int)0, (int)(ls.count), ls.cells[ls.count]);
            //@ assert ls.cells[ls.count] == qp;
            //@ assert listLR(ls, ls.cells[0], (int)0, ls.count, qp);
        } else {
            nfp = fp->cdr->cdr;
            lst_t nsp = sp->cdr;
            sp->cdr = bp;
            tortoise_hare(sp, nsp, nfp, qp) /*@ ghost (ls, k + 1) */;
        }
    }
}

#endif // CONST_SPACE_IMPL
#endif // CONST_SPACE_H
