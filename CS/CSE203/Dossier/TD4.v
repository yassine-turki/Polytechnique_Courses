Require Import ssreflect.


(* We import the following library which gives us a notation for
   the comparision between nat's   *)
Require Import Nat.
Check (leb 3 4).
Eval compute in (3 <=? 4).
Eval compute in (4 <=? 3).



(* The library ssrbool adds a shortcut where booleans can be 
   viewed as propositions. If b is of type bool, it can be 
   viewd as the proposition b = true. *)

Require Import ssrbool.

Check true.

Check (is_true true).

Lemma ex_true : true.
Proof.
reflexivity.
Qed.
(* in general we will rather use the 'trivial' tactic though *)

(* The following command is explained a few lines below *)
Set Implicit Arguments.


(* We define lists as seen; but this time the type of the arguments
   is a parameter. We will be able to have lists for any type.   
   So list : Type -> Type     *)
Inductive list (A : Type) :=
| nil 
| cons : A -> list A -> list A.

Check nil.
Check cons.
(* You see the type A is an argument of nil and cons *)

(* The empty list of nat's  : *)
Check (nil nat).

(* Because of implicit arguments, we can ommit the argument A for 
   cons - it is guessed by the system : *)
Check (cons 1 (cons 2 (nil nat))).

(* We can also often let the system guess the argument of nil : *)
Check (cons 1 (cons 2 (nil _))).


(* A pattern matching :  *)
(* in some versions of Coq you may not have to mention 
   the argument of nil *)

Fixpoint app A (l1 : list A) l2 :=
  match l1 with
  | nil _ => l2  (* here *)
  | cons n l => cons n (app l l2)
  end.


(* examples of adding commands into intro-patterns *)

Lemma app_nil : forall A (l : list A), app l (nil _) = l.
Proof.
move => A.
(* try first 
elim => [ | n l hl].
 *)
(* adding /= forces a 'simpl'
elim => [ | n l hl] /=.
 *)
(* adding //= does simpl + trivial + try discriminate : *)
elim => [ | n l hl] //=.
rewrite hl.

(* The tactic 'done' corresponds to simpl+trivial+try discriminate *)
done.
Qed.

(* one can replace "rewrite hl; done" by  "by rewrite hl." *) 


(* Define the function which computes the length of a list *)
Fixpoint length A (l : list A) :=
  match l with
  | nil _ => 0
  | cons _ m => S(length m)
  end.


Lemma app_length : forall A (l1 : list A) l2,
    length (app l1 l2) = (length l1) + (length l2).
Proof.
move => A.
elim => [| x l hl] l2 //=.  
by rewrite hl.
Qed.


(* The following property states that a nat is less than the 
   first element of a list - if it exists. *)
Definition le_head (n:nat)(l : list nat) :=
  match l with
  | nil _ => True
  | cons m _ => n <=? m
  end.

(* Use le_head to define what is means for a (list nat) to be 
   sorted in increasing order   *)
Fixpoint sorted l :=
  match l with
  | nil _ => True
  | cons n l => (le_head n l) /\ (sorted l)
  end.


Definition l123 := (cons 1 (cons 2 (cons 3 (nil _)))).

Lemma s123 : sorted l123.
Proof.
do 4 (split; trivial).
Qed.

(* Using the  <=?  construct, define a function 
   insert : nat -> list nat -> list nat
   which inserts a nat in a sorted list  *)

Fixpoint insert n l :=
  match l with
  | nil _ => cons n (nil _)
  | cons m l' =>
    if n <=? m then cons n l
    else cons m (insert n l')
  end.


(* Use insert to define a simple sorting function *)
(* insertion_sort : list nat -> list nat.  *)


Fixpoint insertion_sort l :=
  match l with
  | nil _ => nil _
  | cons x l => insert x (insertion_sort l)
  end.

(* Test your function on an example *)
Eval compute in
    (insertion_sort (cons 5 (cons 3 (cons 2 (cons 4 (cons 1 (nil _))))))).


(* What is the complexity of insetion_sort ? *)
(* answer in the comment *)


(* Now we will do two things:
 1 - prove that insertion_sort is indeed a sorting function
 2 - define a more efficient sorting function
*)


(* 1-a : Insertion sort preserves the content of the list. 
   In this part we show that the elements are the same
   at the end of the sorting *)


Fixpoint elem (n:nat) l :=
  match l with
  | nil _ => False
  | cons m l => n = m \/ elem n l
  end.

Lemma ins_elem1 : forall l n m, elem m l -> elem m (insert n l).
Proof.
elim => [| p l hl] n m //=.
move => [e | e]; case (_ <=? _); simpl; auto.
Qed.

Lemma eqn_refl : forall n, n =? n.
elim => [|n e]//=.
Qed.

Lemma eqn_eq : forall n p, n =? p -> n=p.
elim => [|n hn][| p]//= e.
rewrite (hn p) //=.  
Qed.


Lemma ins_elem2 : forall l n, elem n (insert n l).
Proof.
elim => [| p l hl] n //=.
 auto.
case (_ <=? _); simpl; auto.
Qed.


Lemma ins_elem3 : forall l n p, elem p (insert n l) -> p=n \/ elem p l.
Proof.
elim => [| m l hl] n p //=.
case (_ <=? _); simpl; auto.
move => [e | e]; auto.
case: (hl n p e).
 auto.
auto.
Qed.




Lemma insertion_sort_elem1 :
  forall l n, elem n l -> elem n (insertion_sort l).
Proof.
elim => [|m l hl] n //=.
move => [e | e].
  rewrite e; apply ins_elem2.
apply ins_elem1; auto.
Qed.

Lemma insertion_sort_elem2 :
  forall l n, elem n (insertion_sort l) -> elem n l.
Proof.
elim => [|m l hl] n //= e.
case: (ins_elem3 _ m n e).
  auto.
by move => h; right; apply hl.
Qed.

(* Question : is this property totally satisfying ? *)


(* 1-b We now prove that the result of the sorting function is indeed
   sorted *)

(* this technical lemma we already saw in the previous class *)
Lemma leb_trans : forall n m p,
    n <=? m -> m <=? p -> n<=? p.
Proof.
elim => [|n hn][|m][|p]//=.
apply hn.
Qed.

(* This one is easy too *)
Lemma leb_anti : forall n m, n <=? m = false -> m <=? n.
Proof.
elim => [| n hn][| m]//=.
by move => nm; apply hn.
Qed.

(* We want to show that insert preserves the property sorted
   One possibility is to prove first this stronger lemma which
   is a good induction property *)

(* We give the begining of the proof in order to show the use of
   the case tactic here *)
Lemma ins_sorted_aux : forall l n,
    sorted l ->
    (sorted (insert n l))
    /\ (forall m, m<=? n ->
                  le_head m l ->
                  le_head m (insert n l)).
Proof.
(* We do an induction over l, move n up *)
elim => [| m l hl]//= n [h1 h2].

(* we get the two induction hypotheses *)
move: (hl n h2) => [h3 h4].

(* Now the trick : we do a case analysis over (n <=? m) but keep track
  wether its value is true, resp. false *)
case nm : (_ <=? _) => /=; do 3 (try split; trivial).
apply h4; trivial.
by apply leb_anti.
Qed.

(* The lemma we wanted is now an easy consequence of the previous one *)
Lemma ins_sorted : forall l n,
    sorted l ->
    (sorted (insert n l)).
Proof.
by move => l n sl; case (ins_sorted_aux l n sl).
Qed.

Lemma insertion_sort_sorted : forall l, sorted (insertion_sort l).
Proof.
elim => [|x l hl]//=.
by apply ins_sorted.
Qed.


(* 2 A more efficient sorting algorithm *)

(* We use this function which merges two sorted lists into
   one sorted list 
  We give the code because the syntex is a little tricky in order
  to "explain" to Coq the it terminates  *)

Fixpoint merge l1 l2 :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | nil _, t2 => t2
  | t1, nil _ => t1
  | cons n1 m1, cons n2 m2=>
    if n1 <=? n2 then
      cons n1 (merge m1 l2) 
    else 
      cons n2 (merge_aux m2)      
  end
  in merge_aux l2.




Eval compute in
    merge (cons 1 (cons 3 (nil _)))(cons 2 (nil _)).


Inductive tree :=
| Leaf
| Node : nat -> tree -> tree -> tree.


Definition le_tree n t :=
  match t with
  | Leaf => True
  | Node m _ _ => n <=? m = true
  end.


Fixpoint heap t :=
  match t with
  | Leaf => True
  | Node n t1 t2 =>
    le_tree n t1 /\ le_tree n t2  /\
    heap t1 /\ heap t2
  end.


Fixpoint ins_tree n t :=
  match t with
  | Leaf => (Node n Leaf Leaf)
  | Node m t1 t2 =>
    if n <=? m then
      (Node n (ins_tree m t2) t1)
    else
      (Node m (ins_tree n t2) t1)
  end.

(* define a function which transforms an usorted list into a tree
   which has the heap property (and is thus partly sorted)  *)

Fixpoint to_heap l :=
  match l with
  | nil _ => Leaf
  | cons a l =>
    ins_tree a (to_heap l)
  end.

(* define a function which transforms a heap into a sorted list 
   with the same elements *)

Fixpoint to_list t :=
  match t with
  | Leaf => nil _
  | Node a t1 t2 => cons a (merge (to_list t1)(to_list t2))
  end.

(* use the previous functions to define a new sorting function *)

Definition heap_sort l := to_list (to_heap l).

(* test it *)
Eval compute in
    heap_sort (cons 3 (cons 5 (cons 1 (cons 2 (cons 4 (nil _)))))).

(* Can you see or guess things about the complexity of this 
   new sorting function ? *)


(* Proving some properties about heapsort *)
Lemma merge_elem1 : forall l1 l2 n, elem n l1 -> elem n (merge l1 l2).
Proof.
elim => [| n1 l1 hl1]; elim => [| n2 l2 hl2] n //=.
move => [ -> | e] /=; case: (_ <=? _) => //=; auto.
Show.
  right.
  apply hl2; simpl; auto.
right.
apply hl2; simpl; auto.
Qed.

Lemma merge_elem2 : forall l1 l2 n, elem n l2 -> elem n (merge l1 l2).
Proof.
elim => [| n1 l1 hl1]; elim => [| n2 l2 hl2] n //=.
move => [ -> | e] /=; case: (_ <=? _) => //=; auto.
  right.
  apply hl1; simpl; auto.
right.
apply hl1; simpl; auto.
Qed.

Lemma merge_elem3 :  forall l1 l2 n, elem n (merge l1 l2) ->
                                     (elem n l1)\/(elem n l2).
elim => [| n1 l1 hl1]; elim => [| n2 l2 hl2] n //=.
  move => [e|e]; auto.
  move => [e|e]; auto.
case: (_ <=? _) => //=; auto.
  move => [e|e]; auto.
  case: (hl1 _ n e); auto.
  move => [e|e]; auto.
fold merge in e.  
case (hl2 n e); simpl; auto.
Qed.


(* elements of a tree *)

Fixpoint telem n t :=
  match t with
  | Leaf => False
  | Node m t1 t2 => n=m \/ telem n t1 \/ telem n t2
  end.


Lemma inst_elem1 : forall t n, telem n (ins_tree n t).
Proof.
elim => [| m t1 ht1 t2 ht2] n //=.
  auto.
case: (_ <=? _) => //=; auto.
Qed.

Lemma inst_elem2 : forall t n m, telem n t -> telem n (ins_tree m t).
Proof.
elim => [| m t1 ht1 t2 ht2] n //= p.
case:  (_ <=? _) => //=; auto;
 move => [->|[e|e]]; auto; right; left;
 apply inst_elem1.
Qed.

Lemma inst_elem3 : forall t n m, telem n (ins_tree m t) ->
                                 n = m \/ telem n t.
Proof.
elim => [| p t1 ht1 t2 ht2] n m //=.
 move =>[->|[f|f]]//=; auto.
 case:  (_ <=? _) => //=; auto;
    move => [->|[e|e]]; auto; case: (ht2 _ _ e); auto.  
Qed.

Lemma to_heap_elem1 : forall l n,
    elem n l -> telem n (to_heap l).
Proof.
elim => [|m l hl]n//=.
move =>[->|e].
 apply inst_elem1.
apply inst_elem2.
by apply hl. 
Qed.

Lemma to_list_elem1 : forall t n,
    telem n t -> elem n (to_list t).
Proof.
elim => [|m t1 ht1 t2 ht2]n//=.
move=>[e|[e|e]]; auto; right.  
 apply merge_elem1; auto.      
apply merge_elem2; auto.
Qed.

Lemma heapsort_elem1 : forall n l,
    elem n l -> elem n (heap_sort l).
Proof.
move => n l e; apply to_list_elem1.  
apply to_heap_elem1; auto.
Qed.

Lemma to_heap_elem2 : forall l n, telem n (to_heap l) -> elem n l.
Proof.
elim => [|m l hl]n//= e.
case: (inst_elem3 _ _ _ e); auto.
Qed.

Lemma to_list_elem2 : forall t n, elem n (to_list t) -> telem n t.
Proof.
elim => [|m t1 ht1 t2 ht2]n //=.  
move => [e|e]; auto.  
case: (merge_elem3 _ _ _ e); auto.
Qed.

Lemma heap_sort_elem2 : forall l n, elem n (heap_sort l) -> elem n l.
Proof.
move => l n e.
apply to_heap_elem2.
by apply to_list_elem2.
Qed.



Lemma merge_sorted_aux :
  forall l1 l2,
    sorted l1 ->
    sorted l2 ->
       sorted (merge l1 l2)
       /\forall x, le_head x l1 ->
                   le_head x l2 ->
                   le_head x (merge l1 l2).
Proof.
elim =>[| n1 l1 hl1]; elim => [| n2 l2 hl2]//= [s1 h1] [s2 h2].
case n12 : (_ <=? _); simpl.
  by split; auto; split; apply hl1;auto.
split; trivial; split; trivial; case: (hl2) => //= h hh; trivial.
by apply hh; trivial; apply leb_anti.
Qed.

Lemma merge_sorted l1 l2 : sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
by move => sl1 sl2; case (merge_sorted_aux l1 l2 sl1 sl2).
Qed.



Lemma le_tree_trans : forall n m t,
    n <=? m -> le_tree m t -> le_tree n t.
Proof.
move => n m [| r t1 t2]//=.
apply leb_trans.
Qed.

  
Lemma ins_heap_aux :
  forall t n, heap t ->
              heap (ins_tree n t)
              /\forall m, m <=? n = true ->
                          le_tree m t  ->
                          le_tree m (ins_tree n t).
Proof.
elim => [| m t1 iht1 t2 iht2] //= n [mt1 [mt2 [ht1 ht2]]].
move: (iht2 n ht2) => [iht11 iht12].
move: (iht2 m ht2) => [iht21 iht22].
case nm: (_ <=? _) => /=; do 4 (try split; auto).
- apply iht22; trivial.
  by apply le_tree_trans with m.
- by apply le_tree_trans with m.
- apply iht12; trivial.
  by apply leb_anti.
Qed.


(* Possible additional work *)
(* Show that insertion sort returns a permutation of the original list *)

(* We fist axiomatize permuations *)

Parameter permutation : forall A, list A -> list A -> Prop.

Axiom perm_refl : forall A (l : list A), permutation l l.

Axiom perm_app : forall A (l1 : list A) l2 x,
    permutation (cons x (app l1 l2))(app l1 (cons x l2)).

Axiom perm_cons : forall A (l1 : list A) l2 x,
    permutation l1 l2 -> permutation (cons x l1)(cons x l2).

Axiom perm_trans : forall A (l1 : list A) l2 l3,
    permutation l1 l2 -> permutation l2 l3 -> permutation l1 l3.

Axiom perm_sym : forall A (l1 : list A) l2, permutation l1 l2 -> permutation l2 l1.

Lemma ins_perm : forall n l, permutation (cons n l) (insert n l).
move => n; elim => [| m l hl]//=.
 apply perm_refl.
case (_ <=? _).
 apply perm_refl.
apply perm_trans with (cons m (cons n l)).
 apply (perm_app (cons m (nil _)) l n).
apply perm_cons; assumption.
Qed.

Lemma sort_perm : forall l, permutation l (insertion_sort l).
Proof.
elim => [| n l hl] //=.
 apply perm_refl.
apply perm_trans with (cons n (insertion_sort l)).
  apply perm_cons; assumption.
 apply ins_perm.
Qed.

Lemma ins_heap :
xs  forall t n, heap t ->
              heap (ins_tree n t).
Proof.
by move => t n ht; case: (ins_heap_aux t n ht).
Qed.

Lemma to_heap_heap : forall l,
    heap (to_heap l).
Proof.
elim => [| n l hl]//=.
by apply ins_heap.
Qed.

Lemma to_list_sorted :
  forall t, heap t ->
            sorted (to_list t)
          /\forall m, le_tree m t -> le_head m (to_list t). 
Proof.
elim => [|n t1 iht1 t2 iht2]//=.
move => [nt1 [nt2 [ht1 ht2]]].
move: (iht1 ht1) => [iht11 iht12].
move: (iht2 ht2) => [iht21 iht22].
case: (merge_sorted_aux _ _ iht11 iht21) => [h1 h2].
split; auto.
Qed.




(* A3 - pasting it together *)
Lemma heap_sorted :
  forall l, sorted (heap_sort l).
Proof.
move => l; unfold heap_sort; simpl.
case: (to_list_sorted (to_heap l)); trivial.
by apply to_heap_heap.
Qed.

