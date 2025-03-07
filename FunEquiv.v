From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path zify.
Require Import Eqdep.
(* From mathcomp.algebra Require Import ssrint. *)
Require Import FunInd.
From Equations Require Import Equations.

Equations isSortedR (l: seq nat) : bool := 
  isSortedR [::]          := true;
  isSortedR (head :: tail) := loop head tail

  where 
    loop : nat -> seq nat -> bool :=
    loop p [::]    := true;
    loop p (x :: xs) := if p <= x then loop x xs else false.
 
Equations isSortedB (l : seq nat) : bool := 
isSortedB [::] := true;  
isSortedB (lhead :: ltail) :=
    if ltail is head' :: tail'
    then if lhead > head' then false else isSortedB ltail
    else true.

  
Lemma isSortedB_correctB l : isSortedB l = isSortedR l.
Proof.
  apply (isSortedB_elim (fun l res => res = isSortedR l))=>//= h t.
  (* Oh my gosh, what an ugly goal, can I save it into a variable? *)
  (* on another thought, I don't need it for elimination... *)
  case: t=>//={l} h' t /(_ h t) Hi.
  case: ifP=> Eh; last first.
  - have G: h' >= h by apply: (@contraFleq (h' < h) h h').
    suff H: isSortedR [:: h, h' & t] = isSortedR [:: h' & t] by rewrite H.
    by rewrite !isSortedR_equation_2 =>/=; rewrite G. 
  by rewrite isSortedR_equation_2 isSortedR_clause_2_loop_equation_2 leqNgt Eh.
Qed.  
 
(* Same proof, different induction principle *) 
Lemma isSortedB_correctR l : isSortedB l = isSortedR l.
Proof. 
  apply (isSortedR_elim
    (fun l res => isSortedB l = res)
    (fun _ _ p l loopres => isSortedB (p::l) = loopres))=>//= head tail p x xs <-.
  rewrite isSortedB_equation_2.
  case: ifP; rewrite ltnNge; first by rewrite -eqbF_neg=>/eqP->.
  by rewrite Bool.negb_false_iff =>->.
Qed.


(* Vova's proof via induction on isSortedB *)
Lemma isSortedB_correct' l : isSortedB l = isSortedR l.
Proof.
  funelim (isSortedB l)=> //.
  case: ltail H=> // ?? IHtail.
  simp isSortedR; case: ifP.
  { simp loop; case: ifP=> //; lia. }
  rewrite IHtail //; simp isSortedR loop; case: ifP=> //;  lia.
Qed. 

(* ************************************************************************

Examples from https://dl.acm.org/doi/10.1145/3591258

************************************************************************ *)
(* 
def isSortedR(l: List[Int]): Boolean =
  def loop(p: Int, l: List[Int]): Boolean = l match
    case Nil() => true
    case Cons(x, xs) if (p <= x) => loop(x, xs) 
    case _ => false
    if (l.isEmpty) true else loop(l.head, l.tail)
*)

(*
def isSortedB(l: List[Int]): Boolean = 
  if (l.isEmpty)
    true
  else if (!l.tail.isEmpty && l.head > l.tail.head)
    false
  else
  isSortedB(l.tail)
*)

(*
def isSortedC(l: List[Int]): Boolean =
  def chk(l: List[Int], p: Int, a: Boolean): Boolean =
  if (l.isEmpty) a
  else if (l.head < p) false else chk(l.tail, l.head, a)
  if (l.isEmpty) true
  else chk(l, l.head, true)
*)

(*
def isSortedA(l: List[Int]): Boolean =
  def leq(cur: Int, next: Int): Boolean = cur < next 
  def iter(l: List[Int]): Boolean =
  if (l.isEmpty) true
  else if (l.tail.isEmpty) true
  else leq(l.head, l.tail.head) && iter(l.tail)
  if (l.size < 2) true
  else l.head <= l.tail.head && iter(l.tail)
*)