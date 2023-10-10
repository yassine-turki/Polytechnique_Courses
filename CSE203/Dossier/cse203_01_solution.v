From mathcomp Require Import all_ssreflect.

Parameter A B C D : Prop.
(* `move` allows giving a name to the first (top) assumption of
 * the current goal. For example: *)

Lemma move_ex : A -> B -> A.
Proof.
(* Introduce the assumptions `A` & `B` with respective names
 * `hA` and `hB`. *)
move=> hA hB.
Abort.
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

Lemma ex0 : A -> A.
Proof.
move=> h.
assumption.
Qed.

Lemma ex1 : forall A : Prop, A -> A.
Proof.
move=> A h.
assumption.
Qed.
  
Lemma ex2 : (A -> B) -> (B -> C) -> A -> C.
Proof.
move=> hAB hBC hA.
apply hBC.
apply hAB.
assumption.
Qed.

Lemma ex3 : (A -> B -> C) -> (B -> A) -> B -> C.
Proof.
move=> hABC hBA hB.
apply hABC.
+ apply hBA.
  assumption.
+ assumption.
Qed.

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
+ move=> h.
  case: h => [hA hB].
  split.
  * assumption.
  * assumption.
+ move=> h.
  case: h => [hB hA].
  split.
  * assumption.
  * assumption.
Qed.

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
+ move=> h.
  case: h => [hA | hB].
  * right.
    assumption.
  * left.
    assumption.
+ move=> h.
  case: h => [hB | hA].
  * right.
    assumption.
  * left.
    assumption.
Qed.

Lemma disj_ex2 : A /\ B -> A \/ B.
Proof.
move=> h.
case: h => [hA hB].
left. (* `right` would also work *)
assumption.
Qed.

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
move=> hA hNA.
apply hNA.
assumption.
Qed.

Lemma not_ex2 :  (A -> B) -> ~B -> ~A.
Proof.
move=> hAB hNB hA.
apply hNB.
apply hAB.
assumption.
Qed.

Lemma not_ex3 : ~ ~(A \/ ~A).
Proof.
move=> h.
apply h.
right.
move=> hA.
apply h.
left.
assumption.
Qed.

Lemma not_ex4 :  (A \/ B) /\ C <-> (A /\ C) \/ (B /\ C).
Proof.
split.
+ move=> h.
  case: h => [hAB hC].
  case: hAB => [hA | hB].
  * left.
    split.
    - assumption.
    - assumption.
  * right.
    split.
    - assumption.
    - assumption.
+ move=> h.
  case: h => [hAC | hBC].
  * case: hAC => [hA hC].
    split.
    - left.
      assumption.
    - assumption.
  * case: hBC => [hB hC].
    split.
    - right.
      assumption.
    - assumption.
Qed.

Lemma not_ex5 : (A /\ B) \/ C <-> (A \/ C) /\ (B \/ C).
Proof.
split.
+ move=> h.
  case: h => [hAB | hC].
  * case: hAB => [hA hB].
    split.
    - left.
      assumption.
    - left.
      assumption.
  * split.
    - right.
      assumption.
    - right.
      assumption.
+ move=> h.
  case: h => [hAC hBC].
  case: hAC => [hA | hC].
  * case: hBC => [hB | hC].
    - left.
      split.
      + assumption.
      + assumption.
    - right.
      assumption.
  * right.
    assumption.
Qed.