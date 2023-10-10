(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.

(* Predicates                                                           *)
(* ==================================================================== *)

Lemma p1 (P : nat -> Prop) (n : nat) : P n ->  P n.
Proof.
move=> h.
apply h.
Qed.

(* Quantifiers                                                          *)
(* ==================================================================== *)

Parameter P : nat -> Prop.
Parameter Q : nat -> Prop.

Axiom PQ : forall n, P n -> Q n.

Lemma q1 : (P 3) -> exists x, Q x.
Proof.
move=> hP3.
exists 3.
apply PQ.
assumption.
Qed.

Lemma q1' : (exists x, P x) -> exists x, Q x.
Proof.
move=> h.
case: h => [x0 hPx0].
exists x0.
apply PQ.
assumption.
Qed.

Lemma q2 : ~(exists x, P x) -> forall x, ~P x.
Proof.
move=> hNP x hPx.
case: hNP.
exists x.
apply hPx.
Qed.

(* Here you may want to use the tactic  apply ... with ... *)
Lemma q3 : (forall x, ~P x) -> ~(exists x, P x).
Proof.
move=> hNPx hPx.
case: hPx => [x0 hPx0].
apply hNPx with x0.
assumption.
Qed.

Lemma q4 (R : nat -> nat -> Prop) :
  (exists x, forall y, R x y) -> (forall y, exists x, R x y).
Proof.
move=> h y.
case: h => [x0 h].
exists x0.
apply h.
Qed.

(* Leibniz equality                                                     *)
(* ==================================================================== *)

Definition Leibniz (T:Type) (x : T) :=
  fun y => forall P : T -> Prop, (P y) -> (P x).

Lemma Lte : forall T x y, Leibniz T x y -> x = y.
Proof.
move=> T x y eq_xy.
apply eq_xy.
reflexivity.
Qed.

Lemma etL : forall T x y, x = y -> Leibniz T x y.
Proof.
move=> T x y eq_xy.
rewrite eq_xy.
move=> P hPy.
assumption.
Qed.

(* Do the following ones without using the two previous lemmas          *)
Lemma L_sym : forall T x y, Leibniz T x y -> Leibniz T y x.
Proof.
move=> T x y eq_xy P hPx.
pose R z := P z -> P y.
apply (eq_xy R).
+ move=> hPy.
  assumption.
+ assumption.
Qed.

Lemma L_trans : forall T x y z,
  Leibniz  T x y -> Leibniz T y z ->  Leibniz T x z.
Proof. 
move=> T x y z eq_xy eq_yz.
apply eq_xy.
apply eq_yz.
Qed.

(* Using negation                                                       *)
(* ==================================================================== *)
Lemma ex_neg :forall A B : Prop, A -> ~A -> B.
Proof.
move=> A B a na.

(* The following command eliminates the False in 'na' and then asks to  *)
(* prove the assumption A left of the -> in ~A                          *)
case na.

assumption.
Qed.


(* Classical reasonning                                                 *)
(* ==================================================================== *)

(* By default, in Coq, one does not have the principle that any         *)
(* proposition is either true or false (the excluded middle).  We will  *)
(* come back to the reason behind this surprising fact in later         *)
(* lessons. But it is possible to assume the excluded middle as an      *)
(* axiom.                                                               *)

(* Here we start by assuming another classical axiom                    *)
Axiom DNE : forall A : Prop, ~(~A) -> A.

(* Show this axiom entails the excluded middle:                         *)
(* Difficulty: HARD                                                     *)
Lemma excluded_middle : forall A:Prop, A \/ ~A.
Proof.
move=> A.
apply DNE.
move=> hNEM.
apply hNEM.
right.
move=> hA.
apply hNEM.
left.
assumption.
Qed.

Lemma cl1 : exists x, (exists y, P y) -> P x.
Proof.
(* See here how one can use the excluded_middle "lemma" by              *)
(* instantiating the universally quantified variable A                  *)
move: (excluded_middle (exists x, P x)).

(* now finish the proof                                                 *)
move=> h.
case: h => [hPx|hNPx].
+ case: hPx => [x0 Px0].
  exists x0.
  move=> _.
  assumption.
+ exists 0.
  move=> hPx.
  case: hPx => [x0 hPx0].
  case: hNPx.
  exists x0.
  assumption.
Qed.

(* The following lemma is known as the "drinker's paradox": In any      *)
(* pub, there is one person x such that, if that person drinks, the     *)
(* everybody in the pub also drinks                                     *)

(* Formally, it is a slightly more complicated variant of the previous  *)
(* lemma.                                                               *)
(* Difficulty: HARD                                                     *)
Lemma drinker_paradox (P : nat -> Prop) :
  exists x : nat, forall y : nat, P x -> P y.
Proof.
case: (excluded_middle (exists x, ~P x)) => h.
+ case: h => [x0 hNPx0].
  exists x0.
  move=> y.
  move=> hPx0.
  case: hNPx0.
  assumption.
+ exists 0.
  move=> y.
  move=> _.
  case: (excluded_middle (P y)).
  - move=> hPy.
    assumption.
  - move=> hNPy.
    case: h.
    exists y.
    assumption.
Qed.
