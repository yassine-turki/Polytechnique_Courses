(* ====================================================================
 * We start by loading a few libraries and declaring some
 * propositional variables.
 * ==================================================================== *)

Require Import ssreflect.

Parameter A B C D : Prop.

(* ====================================================================
 * Introducing the "move" tactic
 * ==================================================================== *)

(* `move` allows giving a name to the first (top) assumption of
 * the current goal. For example: *)

Lemma move_ex : A -> B -> A.
Proof.
(* Introduce the assumptions `A` & `B` with respective names
 * `hA` and `hB`. *)
move=> hA hB.
Abort.

(* ====================================================================
 * Introducing the "assumption" tactic
 * ==================================================================== *)

(* `assumption` closes a goal when it can be discharged from an
 * assumption. For example: *)

Lemma assumption_ex : A -> B -> A.
Proof.
(* Introduce the assumptions `A` & `B` with respective
 * names `hA` and `hB`. *)
move=> hA hB.
(* The goal can be solved by `hA` *)
assumption.
Qed.

(* It is also possible to close the goal by explicitly giving the name
 * of the assumption, using `apply`: *)

Lemma apply_ex : A -> B -> A.
Proof.
(* Introduce the assumptions `A` & `B` with respective names
 * `hA` and `hB`. *)
move=> hA hB.
(* The goal can be solved by `hA` *)
apply hA.
Qed.

(* ====================================================================
 * Some basic propositional reasonning
 * ==================================================================== *)

Lemma ex0 : A -> A.
Proof.
move => a.
exact a.
Qed.

Lemma ex1 : forall A : Prop, A -> A.
move=>a.
move=>b.
exact b.
Qed.
  
Lemma ex2 : (A -> B) -> (B -> C) -> A -> C.
Proof.
move => ab bc a.
apply bc.
apply ab.
assumption.
Qed.


Lemma ex3 : (A -> B -> C) -> (B -> A) -> B -> C.
Proof.
move=> abc ba b.
apply abc.
apply ba.
apply b.
assumption.
Qed.

(* ====================================================================
 * With conjunctions
 * ==================================================================== *)

(* examples *)

Lemma demo_conj1 : (A /\ B) -> A.
Proof.
move=> h. case: h => [a b]. exact a.
Qed.

Lemma demo_conj2 : A -> B -> A /\ B.
Proof.
move=> a b; split.
+ trivial.
+ trivial.
Qed.

(* your turn *)

Lemma conj_ex1: A /\ B <-> B /\ A.
Proof.
split.
+move=>c.
case c => [a b].
split.
exact b.
exact a.
+move=>d.
case d=> [b a].
split .
exact a.
exact b.
Qed.

(* ====================================================================
 * With disjunctions
 * ==================================================================== *)

(* examples *)

Lemma demo_disj1 : A -> A \/ B.
Proof.
move=> a. left. trivial.
Qed.

Lemma demo_disj2 : B -> A \/ B.
Proof.
move=> a. right. trivial.
Qed.

Lemma demo_disj3 : A \/ B -> C.
move=> h. case: h => [a | b].    (* gives two subgoals *)
Abort.

(* Your turn *)

Lemma disj_ex1 :  A \/ B <-> B \/ A.
Proof.
split.
+move =>p1.
case p1=>[b | a].
right.
assumption.
left.
assumption.
+move=>p2.
case p2=>[a|b].
right.
assumption.
left.
assumption.
Qed.


Lemma disj_ex2 : A /\ B -> A \/ B.
Proof.
move =>ab.
case ab=>[a b].
right.
assumption.
Qed.

(* ====================================================================
 * For negations
 * ==================================================================== *)

Print not.  (* not A (or ~A) is a shorthand for (A -> False) *)

(* examples *)

Lemma demo_not1 : False -> A.
Proof.
(* We can prove any goal from False *)
move=> h. case: h.
Qed.

(* Your turn *)

Lemma not_ex1 : A -> ~(~A).
Proof.
move=>a na.
apply na.
assumption.
Qed.

Lemma not_ex2 :  (A -> B) -> ~B -> ~A.
Proof.
move => ab nb na.
apply nb.
apply ab.
assumption.
Qed.

Lemma not_ex3 : ~ ~(A \/ ~A).
Proof.
move=> a.
apply a.
right.
move =>na.
apply a.
left.
assumption.
Qed.

Lemma not_ex4 :  (A \/ B) /\ C <-> (A /\ C) \/ (B /\ C).
Proof.
split.
+move=> prop1.
case: prop1=> [ab c]. 
case: ab => [a|d].
left.
split.
assumption.
assumption.
right.
split.
assumption.
assumption.
+move => prop2.
case prop2=> [ac|bc].
case ac=> [ba cb].
split.
left.
assumption.
assumption.
case bc=> [h1 h2].
split.
right.
assumption.
assumption.
Qed.


Lemma not_ex5 : (A /\ B) \/ C <-> (A \/ C) /\ (B \/ C).
Proof.
split.
+move=> prop1.
case:prop1=> [ab|c].
case:ab=>[a b].
split.
left.
assumption.
left.
assumption.
split.
right.
assumption.
right.
assumption.
+move=>prop2.
case:prop2=>[ac bc].
case:ac=> [a|c].
case:bc=> [b|c].
left.
split.
assumption.
assumption.
right.
assumption.
right.
assumption.
Qed.