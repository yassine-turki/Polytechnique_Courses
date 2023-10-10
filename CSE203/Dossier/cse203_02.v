(* -------------------------------------------------------------------- *)
Require Import ssreflect.

(* Predicates                                                           *)
(* ==================================================================== *)

Lemma p1 (P : nat -> Prop) (n : nat) : P n ->  P n.
Proof. 
move => h.
assumption.
Qed.

(* Quantifiers                                                          *)
(* ==================================================================== *)

Parameter P : nat -> Prop.
Parameter Q : nat -> Prop.

Axiom PQ : forall n, P n -> Q n.

Lemma q1 : (P 3) -> exists x, Q x.
Proof. 
move=>P.
exists 3.
apply PQ.
assumption.
Qed.


Lemma q1' : (exists x, P x) -> exists x, Q x.
Proof. 
move =>h.
case: h=> [a b].
exists a.
apply PQ.
assumption.
Qed.

Lemma q2 : ~(exists x, P x) -> forall x, ~P x.
Proof. 
move =>h.
move => h1.
move => h2.
apply h.
exists h1.
apply h2.
Qed.

(* Here you may want to use the tactic  apply ... with ... *)
Lemma q3 : (forall x, ~P x) -> ~(exists x, P x).
Proof.
move => h.
move => h1.
move :h1=>[a b].
apply h with a.
assumption.
Qed.

Lemma q4 (R : nat -> nat -> Prop) :
  (exists x, forall y, R x y) -> (forall y, exists x, R x y).
Proof. 
move => [x px] y.
exists x.
apply px.
Qed.  

(* Leibniz equality                                                     *)
(* ==================================================================== *)

Definition Leibniz (T:Type) (x : T) :=
  fun y => forall P : T->Prop, (P y) -> (P x).

Lemma Lte : forall T x y, Leibniz T x y -> x = y.
Proof. 
move=> T x y.
move =>L. 
apply L.
reflexivity.
Qed.

Lemma etL : forall T x y, x = y -> Leibniz T x y.
Proof.
move=> T x y eq.
rewrite eq.
move=> h1 h2.
assumption.
Qed.


(* Do the following ones without using the two previous lemmas          *)
Lemma L_sym : forall T x y, Leibniz T x y -> Leibniz T y x.
Proof.
move=> T x y L h1.
apply L.
move =>p.
assumption.
Qed.

Lemma L_trans : forall T x y z,
  Leibniz  T x y -> Leibniz T y z ->  Leibniz T x z.
Proof. 
move => T x y z L1 L2 L3 L4.
apply L1.
apply L2.
assumption.
Qed.


(* Using negation                                                       *)
(* ==================================================================== *)
Lemma ex_neg :forall A B : Prop, A -> ~A -> B.
Proof.
move => A B a na.

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
move=>h.
apply DNE.
move => hneg.
apply hneg.
right.
move => fal.
apply hneg.
left.
assumption.
Qed.



Lemma cl1 : exists x, (exists y, P y) -> P x.
Proof.
(* See here how one can use the excluded_middle "lemma" by              *)
(* instantiating the universally quantified variable A                  *)
move: (excluded_middle (exists x, P x)).

(* now finish the proof                                                 *)
move =>h.
case h => [ha|hb].
+case ha=>[a b].
exists a.
move =>py.
assumption.
+exists 5.
move=>PY.
case PY=>[P1 P2].
case: hb.
apply PY.
Qed.



(* The following lemma is known as the "drinker's paradox": In any      *)
(*pub, there is one person x such that, if that person drinks, the      *)
(*everybody in the pub also drinks                                      *)

(* Formally, it is a slightly more complicated variant of the previous  *)
(* lemma.                                                               *)
(* Difficulty: HARD                                                     *)
Lemma drinker_paradox (P : nat -> Prop) :
  exists x : nat, forall y : nat, P x -> P y.
Proof. 
move: (excluded_middle (exists x, ~P x)).
move=>h.
case h=>[a|b].
+case a=>[n np].
exists n.
move =>y.
contradiction.
+exists 5.
move =>y.
move => p5.
case: (excluded_middle(P y)).
trivial.
move =>npy.
case: b.
exists y.
trivial.
Qed.

