Require Import Lia.
Require Import PeanoNat.

Require Import List_Type_more.

(* LIST MANIPULATION *)

Fixpoint nth {A} (l : list A) (a : A) n :=
  match n, l with
  | _, nil => a
  | 0, b :: l => b
  | S n , b :: l => nth l a n
  end.

Lemma nth_correct {A} : forall l (a0 : A) a1 k,
    k < length l ->
    nth l a0 k = nth l a1 k.
Proof with try assumption; try reflexivity.
  induction l; intros a0 a1 k Hlt; try now inversion Hlt.
  destruct k...
  apply Lt.lt_S_n in Hlt.
  apply IHl...
Qed.  

Lemma nth_nth {A} : forall (l1 : list nat) (l2 : list A) a0 k0 k,
    k < length l1 ->
    nth l2 a0 (nth l1 k0 k) = nth (map (fun x => nth l2 a0 x) l1) a0 k.
Proof with try assumption; try reflexivity.
  induction l1; intros l2 a0 k0 k Hlt.
  - inversion Hlt.
  - destruct k...
    simpl.
    apply IHl1.
    simpl in Hlt.
    lia.
Qed.

Lemma nth_ge {A} : forall (l : list A) a k,
    length l <= k ->
    nth l a k = a.
Proof with try reflexivity; try assumption.
  induction l; intros a0 k Hle...
  - destruct k...
  - destruct k.
    + exfalso.
      simpl in Hle; lia.
    + simpl.
      apply IHl.
      simpl in Hle.
      lia.
Qed.

Lemma nth_plus {A} : forall (l1 : list A) l2 k0 k,
    nth (l1 ++ l2) k0 (length l1 + k) = nth l2 k0 k.
Proof with try reflexivity; try assumption.
  induction l1; intros k2 k0 k...
  simpl.
  apply IHl1...
Qed.

Lemma nth_decomp {A} : forall l (a0 : A) k,
    k < length l ->
    {' (la , lb) : _ & prod (length la = k) (l = la ++ (nth l a0 k) :: lb)}.
Proof with try reflexivity; try assumption.
  induction l; intros a0 k Hlt.
  - exfalso; simpl in Hlt; lia.
  - destruct k.
    + split with (nil, l).
      split...
    + simpl in Hlt.
      apply Lt.lt_S_n in Hlt.
      specialize (IHl a0 k Hlt) as ((la & lb) & (Hlen & Heq)).
      split with (a :: la, lb).
      split.
      * rewrite<- Hlen...
      * pattern l at 1.
        rewrite Heq...
Qed.     

Lemma nth_middle {A} : forall la lb (a : A) a0,
    nth (la ++ a :: lb) a0 (length la) = a.
Proof with try reflexivity.
  induction la; intros lb a' a0...
  simpl.
  apply IHla.
Qed.

Lemma nth_left {A} : forall (la : list A) lb a0 n,
    n < length la ->
    nth (la ++ lb) a0 n = nth la a0 n.
Proof with try reflexivity.
  induction la; intros lb a0 n Hlt.
  - simpl in Hlt; lia.
  - destruct n...
    simpl.
    apply IHla.
    simpl in Hlt; lia.
Qed.

Lemma list_ext {A} : forall l1 l2,
    length l1 = length l2 ->
    (forall n (a0 : A), nth l1 a0 n = nth l2 a0 n) ->
    l1 = l2.
Proof with try reflexivity.
  induction l1; intros l2 Hlen H.
  - destruct l2; try now inversion Hlen...
  - destruct l2; try now inversion Hlen.
    replace a0 with a.
    2:{ change a with (nth (a :: l1) a 0).
        change a0 with (nth (a0 :: l2) a 0).
        apply H. }
    apply Nat.succ_inj in Hlen.
    specialize (IHl1 l2 Hlen).
    clear Hlen.
    replace l2 with l1...
    apply IHl1.
    intros n a1.
    refine (H (S n) a1).
Qed.


Lemma cond_In {A} :
  forall l (x : A),
    (exists p, prod (fst p < length l) (nth l (snd p) (fst p) = x)) ->
    In x l.
Proof with try reflexivity; try assumption.
  induction l; intros x [(k , a0) (Hlen & Heq)]; simpl in Hlen, Heq.
  - inversion Hlen.
  - destruct k.
    + left...
    + simpl in Hlen; apply Lt.lt_S_n in Hlen.
      right.
      apply IHl.
      exists (k , a0).
      split...
Qed.

Lemma cond_In_inv {A} :
  forall l (x : A),
    In x l ->
    exists p, prod (fst p < length l) (nth l (snd p) (fst p) = x).
Proof with try reflexivity; try assumption.
  induction l; intros x Hin.
  - inversion Hin.
  - refine (@or_ind (a = x) (In x l) _ _ _ _).
    + intros H.
      exists (0 , a).
      simpl.
      split...
      lia.
    + clear Hin; intros Hin.
      destruct (IHl x Hin) as [(k & a0) (Hlen & Heq)].
      exists (S k , a0).
      split...
      simpl in Hlen |- *; lia.
    + apply in_inv...
Qed.

Lemma cond_In_Type {A} :
  forall l (x : A),
    {' (k , a0) : _ & prod (k < length l) (nth l a0 k = x) } ->
    In_Type x l.
Proof with try reflexivity; try assumption.
  induction l; intros x ((k , a0) & (Hlen & Heq)); simpl in Hlen, Heq.
  - exfalso.
    inversion Hlen.
  - destruct k.
    + left...
    + simpl in Hlen; apply Lt.lt_S_n in Hlen.
      right.
      apply IHl.
      split with (k , a0).
      split...
Qed.

Lemma cond_In_Type_inv {A} :
  forall l (x : A),
    In_Type x l ->
    {' (k , a0) : _ & prod (k < length l) (nth l a0 k = x)}.
Proof with try reflexivity; try assumption.
  induction l; intros x Hin.
  - inversion Hin.
  - destruct Hin.
    + exists (0 , a).
      simpl.
      split...
      lia.
    + destruct (IHl x i) as [(k & a0) (Hlen & Heq)].
      exists (S k , a0).
      split...
      simpl in Hlen |- *; lia.
Qed.

Lemma map_nth {A B} : forall (f : A -> B) l a0 k,
    nth (map f l) (f a0) k = f (nth l a0 k).
Proof with try reflexivity.
  intros f.
  induction l; intros a0 k.
  - destruct k...
  - destruct k...
    rewrite map_cons.
    apply IHl.
Qed.