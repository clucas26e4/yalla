Require Import Lia.
Require Import PeanoNat.
Require Import EqNat.

Require Import Bool_more.
Require Import List_more.
Require Import List_manip.
Require Import Permutation_more.

Ltac splitb := apply andb_true_intro; split.

(* Properties on list nat *)
Lemma UIP_list_nat : forall (l1 l2 : list nat) (p1 p2 : l1 = l2),
    p1 = p2.
Proof with try reflexivity; try assumption.
  intros l1 l2 p1 p2.
  apply Eqdep_dec.UIP_dec.
  apply list_eq_dec.
  apply Nat.eq_dec.
Qed.    
      
(* APP_NAT_FUN *)

Definition app_nat_fun {A} (l : list A) (p : list nat) :=
  match l with
  | nil => nil
  | a :: l => map (fun x => nth (a :: l) a x) p
  end.

Ltac app_nat_fun_unfold l1 l2 a1 n2 :=
  change (app_nat_fun (a1 :: l1) (n2 :: l2)) with ((nth (a1 :: l1) a1 n2) :: (app_nat_fun (a1 :: l1) l2)) in *.

Definition compo l1 l2 : list nat :=
  app_nat_fun l1 l2.

Lemma app_nat_fun_middle {A} : forall l1 l2 (a : A) (p : list nat),
    app_nat_fun (l1 ++ a :: l2) (length l1 :: p) = a :: (app_nat_fun (l1 ++ a :: l2) p).
Proof with try reflexivity; try assumption.
  destruct l1...
  intros l2 a0 p.
  change (app_nat_fun ((a :: l1) ++ a0 :: l2) (length (a :: l1) :: p)) with ((nth ((a :: l1) ++ a0 :: l2) a (length (a :: l1))) :: app_nat_fun ((a :: l1) ++ a0 :: l2) p).
  pattern a0 at 3.
  replace a0 with (nth ((a :: l1) ++ a0 :: l2) a (length (a :: l1)))...
  apply nth_middle.
Qed.

Lemma app_nat_fun_nil {A} : forall (l : list A),
    app_nat_fun l nil = nil.
Proof with try reflexivity.
  destruct l...
Qed.

(** ** incr_all *)

Definition incr_all l k := map (fun x => k + x) l.

Fixpoint Id n :=
  match n with
  | 0 => nil
  | (S n) => 0 :: (incr_all (Id n) 1)
  end.

Lemma incr_all_length : forall l n,
    length (incr_all l n) = length l.
Proof with try reflexivity.
  intros l n.
  unfold incr_all; apply map_length.
Qed.

Lemma incr_all_incr_all : forall l n m,
    incr_all (incr_all l n) m = incr_all (incr_all l m) n.
Proof with try reflexivity; try assumption.
  induction l; intros n m...
  simpl.
  rewrite IHl.
  replace (m + (n + a)) with (n + (m + a))...
  lia.
Qed.

Lemma incr_all_0 : forall l,
    incr_all l 0 = l.
Proof with try reflexivity; try assumption.
  induction l...
  simpl; rewrite IHl...
Qed.

Lemma incr_all_plus : forall l n m,
    incr_all l (n + m) = incr_all (incr_all l n) m.
Proof with try reflexivity; try assumption.
  induction l; intros n m...
  simpl.
  rewrite Nat.add_assoc.
  rewrite IHl.
  rewrite (Nat.add_comm n m)...
Qed.

Lemma incr_all_app : forall l1 l2 n,
    incr_all (l1 ++ l2) n = incr_all l1 n ++ incr_all l2 n.
Proof with try reflexivity; try assumption.
  induction l1; intros l2 n...
  simpl.
  rewrite IHl1...
Qed.  

Lemma Id_incr_all_Id : forall n m,
    Id n ++ (incr_all (Id m) n) = Id (n + m).
Proof with try reflexivity; try assumption.
  induction n; intros m.
  - rewrite incr_all_0...
  - simpl.
    replace (incr_all (Id (n + m)) 1) with (incr_all (Id n) 1 ++ incr_all (Id m) (S n))...
    replace (S n) with (n + 1) by lia.
    rewrite incr_all_plus.
    rewrite<- incr_all_app.
    rewrite IHn...
Qed.

(** ** In_nat_bool *)

Fixpoint In_nat_bool (n : nat) (l : list nat) :=
  match l with
  | nil => false
  | k :: l => (beq_nat n k) || (In_nat_bool n l)
  end.

Lemma In_nat_bool_false_tail : forall l n k,
    In_nat_bool n (k :: l) = false ->
    In_nat_bool n l = false.
Proof with try reflexivity; try assumption.
  intros l n k nHin.
  unfold In_nat_bool in nHin.
  change ((fix In_nat_bool (n : nat) (l : list nat) {struct l} : bool :=
               match l with
               | nil => false
               | k :: l0 => (n =? k) || In_nat_bool n l0
               end) n l) with (In_nat_bool n l) in nHin.
  case_eq (In_nat_bool n l); intro Heq...
  revert nHin; case (n =? k); intro nHin; rewrite Heq in nHin; inversion nHin.
Qed. 

Lemma neg_nth_eq : forall l n k0 k,
    In_nat_bool n l = false ->
    k < length l ->
    nth l k0 k <> n.
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin Hlt Heq.
  - inversion Hlt.
  - destruct k.
    + simpl in Heq.
      unfold In_nat_bool in nHin.
      replace (n =? a) with true in nHin ; [inversion nHin | ].
      symmetry; apply Nat.eqb_eq; symmetry...
    + simpl in Heq.
      simpl in Hlt; apply Lt.lt_S_n in Hlt.
      refine (IHl n k0 _ _ Hlt _)...
      apply In_nat_bool_false_tail with a...
Qed.

Lemma cond_negb_In_nat_bool : forall l n,
    (forall k k0,
        k < length l ->
        nth l k0 k <> n) <->
    In_nat_bool n l = false.
Proof with try reflexivity; try assumption.
  intros l n; split; revert n.
  - induction l; intros n H...
    unfold In_nat_bool.
    case_eq (n =? a); intro Heq.
    + exfalso.
      refine (H 0 0 _ _)...
      * simpl; lia.
      * apply Nat.eqb_eq in Heq.
        symmetry...
    + simpl.
      change ((fix In_nat_bool (n0 : nat) (l0 : list nat) {struct l0} : bool :=
                 match l0 with
                 | nil => false
                 | k :: l1 => (n0 =? k) || In_nat_bool n0 l1
                 end) n l) with (In_nat_bool n l).
      refine (IHl n _).
      intros k k0 Hlt Heq'.
      refine (H (S k) k0 _ _)...
      simpl; apply Lt.lt_n_S...
  - induction l; intros n nHin k k0 Hlt Heq.
    + inversion Hlt.
    + destruct k.
      * simpl in Heq.
        unfold In_nat_bool in nHin.
        replace (n =? a) with true in nHin ; [inversion nHin | ].
        symmetry; apply Nat.eqb_eq; symmetry in Heq...
      * simpl in Heq , Hlt.
        apply Lt.lt_S_n in Hlt.
        unfold In_nat_bool in nHin.
        change ((fix In_nat_bool (n : nat) (l : list nat) {struct l} : bool :=
               match l with
               | nil => false
               | k :: l0 => (n =? k) || In_nat_bool n l0
               end) n l) with (In_nat_bool n l) in nHin.
        revert nHin; case (n =? a); intro nHin; try now inversion nHin.
        refine (IHl _ nHin _ _ Hlt Heq).        
Qed.

Lemma cond_In_nat_bool : forall l n,
    {'(k0 , k) : _ & prod (k < length l) (nth l k0 k = n) } ->
    In_nat_bool n l = true.
Proof with try assumption; try reflexivity.
  intros l n x.
  destruct x as ((k0 & k) & (Hlt & Heq)).
  revert k Hlt Heq; induction l; intros k Hlt Heq.
  - inversion Hlt.
  - destruct k.
    + simpl in Heq.
      symmetry in Heq; apply Nat.eqb_eq in Heq.
      unfold In_nat_bool.
      rewrite Heq...
    + simpl in Heq.
      simpl in Hlt; apply Lt.lt_S_n in Hlt.
      unfold In_nat_bool.
      case (n =? a)...
      change ( (fix In_nat_bool (n0 : nat) (l0 : list nat) {struct l0} : bool :=
        match l0 with
        | nil => false
        | k1 :: l1 => (n0 =? k1) || In_nat_bool n0 l1
        end) n l) with (In_nat_bool n l).
      refine (IHl k _ _)...
Qed.  

Lemma cond_In_nat_bool_inv : forall l n k0,
    In_nat_bool n l = true -> 
    {k : _ & prod (k < length l) (nth l k0 k = n) }.
Proof with try assumption; try reflexivity.
  intros l n k0; induction l; intros Hin; try now inversion Hin.
  unfold In_nat_bool in Hin.
  change ((fix In_nat_bool (n : nat) (l : list nat) {struct l} : bool :=
              match l with
              | nil => false
              | k :: l0 => (n =? k) || In_nat_bool n l0
              end) n l) with (In_nat_bool n l) in Hin.
  case_eq (n =? a); intros Heq.
  - apply Nat.eqb_eq in Heq; subst.
    split with 0.
    split...
    simpl; lia.
  - rewrite Heq in Hin.
    clear Heq.
    specialize (IHl Hin) as (k & (Hlt & Heq)).
    split with (S k).
    split...
    simpl; lia. 
Qed.

Lemma In_nat_bool_neq : forall l n k,
    n <> k ->
    In_nat_bool k (n :: l) = In_nat_bool k l.
Proof with try reflexivity; try assumption.
  intros l n k nHeq.
  simpl.
  replace (k =? n) with false...
  symmetry; apply Nat.eqb_neq.
  intros Heq; apply nHeq; symmetry...
Qed.

Lemma In_nat_bool_incr_all : forall l k n,
    In_nat_bool k l = In_nat_bool (n + k) (incr_all l n).
Proof with try reflexivity; try assumption.
  induction l; intros k n...
  assert ((k =? a) = (n + k =? n + a)).
  { case_eq (k =? a); intro Heq.
    - apply Nat.eqb_eq in Heq; subst.
      symmetry; apply Nat.eqb_eq...
    - symmetry.
      apply Nat.eqb_neq.
      intro Heq'.
      apply Plus.plus_reg_l in Heq'; subst.
      apply Nat.eqb_neq in Heq.
      apply Heq... }
  unfold In_nat_bool.
  rewrite H.
  simpl.
  change ((fix In_nat_bool (n0 : nat) (l0 : list nat) {struct l0} : bool :=
        match l0 with
        | nil => false
        | k0 :: l1 => (n0 =? k0) || In_nat_bool n0 l1
        end) k l) with (In_nat_bool k l).
  rewrite (IHl k n)...
Qed.

Lemma negb_In_incr_all : forall l k n,
    k < n ->
    In_nat_bool k (incr_all l n) = false.
Proof with try reflexivity; try assumption.
  induction l; intros k n Hlt...
  simpl.
  assert (k =? n + a = false).
  { apply Nat.eqb_neq.
    intros Heq.
    clear - Hlt Heq.
    revert k Hlt Heq.
    induction n; intros k Hlt Heq.
    - inversion Hlt.
    -  destruct k.
       + inversion Heq.
       + apply Lt.lt_S_n in Hlt.
         inversion Heq.
         apply IHn with k... }
  rewrite H.
  apply IHl...
Qed.

Lemma In_nat_bool_app : forall l1 l2 k,
    In_nat_bool k (l1 ++ l2) = (In_nat_bool k l1) || (In_nat_bool k l2).
Proof with try reflexivity; try assumption.
  induction l1; intros l2 k...
  simpl.
  case (k =? a)...
  rewrite IHl1...
Qed.
Lemma In_nat_bool_middle_true : forall l1 l2 a a0,
                 In_nat_bool a (l1 ++ a0 :: l2) = true ->
                 (a =? a0) || (In_nat_bool a (l1 ++ l2)) = true.
Proof with try reflexivity; try assumption.
  induction l1; intros l2 b a0 Hin...
  simpl in Hin.
  case_eq (b =? a); intros Heq.
  - case (b =? a0)...
    simpl.
    rewrite Heq...
  - rewrite Heq in Hin.
    simpl.
    replace ((b =? a0) || ((b =? a) || In_nat_bool b (l1 ++ l2))) with (((b =? a0) || In_nat_bool b (l1 ++ l2)) || (b =? a)).
    2:{ case (b =? a0); case (In_nat_bool b (l1 ++ l2)) ; case (b =? a)... }
    rewrite IHl1...
Qed.

Lemma In_nat_bool_middle_false : forall l1 l2 a a0,
           In_nat_bool a (l1 ++ a0 :: l2) = false ->
           (a =? a0 = false) /\ (In_nat_bool a (l1 ++ l2) = false).
Proof with try reflexivity; try assumption.
  induction l1; intros l2 b a0 nHin.
  - apply orb_false_iff in nHin...
  - case_eq (b =? a0); intros Heq.
    + apply orb_false_iff in nHin as (_ & nHin).
      specialize (IHl1 l2 b a0 nHin) as (H & _).
      rewrite Heq in H.
      inversion H.
    + split...
      apply orb_false_iff in nHin as (nHeq & nHin).
      apply orb_false_iff.
      split...
      specialize (IHl1 l2 b a0 nHin) as (_ & H)...
Qed.

Lemma In_nat_bool_app_commu : forall l1 l2 a,
    In_nat_bool a (l1 ++ l2) = In_nat_bool a (l2 ++ l1).
Proof with try reflexivity; try assumption.
  induction l1; intros l2 b.
  - rewrite app_nil_r...
  - simpl.
    case_eq (In_nat_bool b (l2 ++ a :: l1)); intros Hin.
    + apply In_nat_bool_middle_true in Hin.
      rewrite IHl1...
    + apply In_nat_bool_middle_false in Hin as (nHeq & nHin).
      rewrite nHeq.
      rewrite IHl1.
      rewrite nHin...
Qed.

Lemma In_nat_bool_Perm: forall l1 l2 a,
    Permutation l1 l2 ->
    In_nat_bool a l1 = In_nat_bool a l2.
Proof with try reflexivity; try assumption.
  intros l1 l2 a Hp.
  induction Hp...
  - simpl; rewrite IHHp...
  - simpl.
    case (a =? y) ; case (a =? x)...
  - transitivity (In_nat_bool a l')...
Qed.
                                
(** ** all_lt *)

Fixpoint all_lt (l : list nat) (n : nat) :=
  match l with
  | nil => true
  | k :: l => (k <? n) && (all_lt l n)
  end.

Lemma all_lt_leq : forall l k n,
    all_lt l k = true ->
    k <= n ->
    all_lt l n = true.
Proof with try reflexivity; try assumption.
  induction l; intros k n Hal Hleq...
  destruct (andb_prop _ _ Hal).
  splitb.
  - apply Nat.ltb_lt.
    unfold lt.
    transitivity k...
    apply Nat.ltb_lt in H...
  - apply IHl with k...
Qed.

Lemma cond_all_lt_false : forall l n k k0,
    k < length l ->
    n <= nth l k0 k ->
    all_lt l n = false.
Proof with try reflexivity; try assumption.
  induction l; intros n k k0 H Hgeq.
  - inversion H.
  - destruct k.
    + simpl.
      replace (a <? n) with false...
      symmetry.
      apply Nat.ltb_nlt.
      intros Hlt.
      simpl in Hgeq; lia.
    + simpl in H.
      apply Lt.lt_S_n in H.
      simpl in Hgeq.
      unfold all_lt.
      case (a <? n)...
      simpl.
      apply IHl with k k0...
Qed.

Lemma cond_all_lt_false_inv : forall l n,
    all_lt l n = false ->
    forall k0,
      { k & prod (k < length l) (n <= nth l k0 k)}.
Proof with try reflexivity; try assumption.
  induction l; intros n nHalt k0.
  - inversion nHalt.
  - unfold all_lt in nHalt.
    case_eq (a <? n); intros Hlt.
    + rewrite Hlt in nHalt.
      simpl in nHalt.
      destruct (IHl n nHalt k0) as (k & (Hlen & Hgeq)).
      split with (S k).
      split...
      simpl.
      apply Lt.lt_n_S...
    + split with 0.
      split.
      * simpl; lia.
      * apply Nat.ltb_nlt in Hlt.
        simpl; lia.
Qed.

Lemma all_lt_middle_true : forall l1 l2 a k,
    all_lt (l1 ++ a :: l2) k = true ->
    all_lt (l1 ++ l2) k = true.
Proof with try reflexivity; try assumption.
  induction l1; intros l2 b k H.
  - apply andb_prop in H as (_ & H)...
  - apply andb_prop in H as (H1 & H2).
    simpl.
    rewrite H1.
    refine (IHl1 _ _ _ H2).
Qed.

Lemma cond_all_lt : forall l n,
    (forall k0 k,
        k < length l ->
        nth l k0 k < n) ->
    all_lt l n = true.
Proof with try reflexivity; try assumption.
  intros l n.
  induction l; intros H...
  splitb.
  - apply Nat.ltb_lt.
    change a with (nth (a :: l) 0 0).
    apply H.
    simpl; lia.
  - apply IHl.
    intros k0 k Hlt.
    change (nth l k0 k) with (nth (a :: l) k0 (S k)).
    apply H.
    simpl; lia.
Qed.

Lemma cond_all_lt_inv : forall l n k0 k,
    k < length l ->
    all_lt l n = true ->
    nth l k0 k < n.
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k Hlt Halt; try now inversion Hlt.
  destruct k.
  - apply andb_prop in Halt as (H & _).
    apply Nat.ltb_lt...
  - apply andb_prop in Halt as (_ & Halt).
    apply IHl...
    simpl in Hlt.
    lia.
Qed.

Lemma all_lt_incr_all : forall l n1 n2,
    all_lt l n1 = all_lt (incr_all l n2) (n2 + n1).
Proof with try reflexivity; try assumption.
  induction l; intros n1 n2...
  simpl.
  rewrite (IHl n1 n2).
  assert (a <? n1 = (n2 + a <? n2 + n1)).
  { case_eq (a <? n1); intros Hleq; symmetry.
    - apply Nat.ltb_lt.
      apply Nat.ltb_lt in Hleq.
      apply Plus.plus_lt_compat_l...
    - apply Nat.ltb_nlt in Hleq.
      apply Nat.ltb_nlt.
      intro Hlt.
      apply Hleq.
      apply Plus.plus_lt_reg_l with n2... }
  rewrite H...
Qed.

Lemma all_lt_Id : forall n, all_lt (Id n) n = true.
Proof with try reflexivity; try assumption.
  induction n...
  simpl; rewrite<- all_lt_incr_all...
Qed.

Lemma all_lt_app : forall l1 l2 n,
    all_lt (l1 ++ l2) n = (all_lt l1 n) && (all_lt l2 n).
Proof with try reflexivity; try assumption.
  induction l1; intros l2 n...
  simpl.
  case (a <? n)...
  rewrite IHl1...
Qed.

Lemma all_lt_In_nat_bool_false : forall l n,
    all_lt l n = true ->
    In_nat_bool n l = false.
Proof with try reflexivity; try assumption.
  induction l; intros n Hal...
  apply andb_prop in Hal as (Hlt & Hal).
  simpl; rewrite (IHl _ Hal).
  replace (n =? a) with false...
  symmetry.
  apply Nat.eqb_neq.
  apply Nat.ltb_lt in Hlt.
  lia.
Qed.
  
(** ** all_distinct *)

Fixpoint all_distinct (l : list nat) :=
  match l with
  | nil => true
  | n :: l => (negb (In_nat_bool n l)) && (all_distinct l)
  end.

Lemma all_distinct_incr_all : forall l n,
    all_distinct l = all_distinct (incr_all l n).
Proof with try reflexivity; try assumption.
  induction l; intros n...
  simpl.
  rewrite (In_nat_bool_incr_all l a n).
  rewrite (IHl n)...
Qed.

Lemma all_distinct_Id : forall n,
    all_distinct (Id n) = true.
Proof with try reflexivity; try assumption.
  induction n...
  splitb.
  + apply negb_true_iff.
    apply negb_In_incr_all.
    apply Nat.lt_0_1.
  + rewrite<- all_distinct_incr_all...
Qed.

Lemma cond_all_distinct : forall l,
    (forall n1 n2 k,
        n1 < length l ->
        n2 < length l ->
        (nth l k n1) = (nth l k n2) ->
        n1 = n2) ->
    all_distinct l = true.
Proof with try assumption; try reflexivity.
  induction l; intros H...
  splitb.
  + apply negb_true_iff.
    apply cond_negb_In_nat_bool.
    intros k k0 Hlt Heq.
    refine (Nat.neq_succ_0 k _).
    refine (H (S k) 0 k0 _ _ _)...
    * simpl; lia.
    * simpl; lia.
  + change ((fix all_distinct (l0 : list nat) : bool :=
               match l0 with
               | nil => true
               | n :: l1 => negb (In_nat_bool n l1) && all_distinct l1
               end) l) with (all_distinct l).
    refine (IHl _).
    intros n1 n2 k Hlt1 Hlt2 Heq.
    apply Nat.succ_inj.
    refine (H (S n1) (S n2) k _ _ _); try now (simpl; lia)...
Qed.

Lemma cond_all_distinct_inv : forall l,
    all_distinct l = true -> (forall n1 n2 k,
                                  n1 < length l ->
                                  n2 < length l ->
                                  (nth l k n1) = (nth l k n2) ->
                                  n1 = n2).
Proof with try assumption; try reflexivity.
  induction l; intros Hal n1 n2 k Hlt1 Hlt2 Heq.
  + destruct n1; inversion Hlt1.
  + destruct n1; destruct n2...
    * simpl in Heq.
      simpl in Hlt2; apply Lt.lt_S_n in Hlt2.
      exfalso.
      refine (neg_nth_eq l a k n2 _ _ _)...
      -- apply andb_prop in Hal as (H1 & _).
         apply negb_true_iff in H1...
      -- symmetry...
    * simpl in Heq.
      simpl in Hlt1; apply Lt.lt_S_n in Hlt1.
      exfalso.
      refine (neg_nth_eq l a k n1 _ _ _)...
      apply andb_prop in Hal as (H1 & _).
      apply negb_true_iff in H1...
    * simpl in *.
      apply Lt.lt_S_n in Hlt1.
      apply Lt.lt_S_n in Hlt2.
      apply eq_S.
      apply andb_prop in Hal as (_ & H2).
      refine (IHl _ _ _ k _ _ _)...
Qed.

Lemma all_distinct_no_head : forall l n,
    all_distinct (n :: l) = true ->
    forall k k0,
      k < length l ->
      nth l k0 k <> n.
Proof with try reflexivity; try assumption.
  intros l n Hal k k0 Hlt.
  apply andb_prop in Hal as (nHin & Hal).
  change ((fix all_distinct (l : list nat) : bool :=
           match l with
           | nil => true
           | n :: l0 => negb (In_nat_bool n l0) && all_distinct l0
           end) l) with (all_distinct l) in Hal.
  refine (neg_nth_eq l n k0 k _ Hlt).
  apply negb_true_iff...
Qed.

Lemma cond_all_distinct_false : forall l k0 k1 k2,
    k1 < length l ->
    k2 < length l ->
    k1 <> k2 ->
    nth l k0 k1 = nth l k0 k2 ->
    all_distinct l = false.
Proof with try reflexivity; try assumption.
  induction l; intros k0 k1 k2 Hlt1 Hlt2 nHeq Heq; try now inversion Hlt1.
  destruct k1; destruct k2.
  - exfalso.
    apply nHeq...
  - simpl.
    replace (negb (In_nat_bool a l)) with false...
    symmetry.
    apply negb_false_iff.
    apply cond_In_nat_bool.
    split with (k0 , k2).
    split.
    + simpl in Hlt2; lia.
    + simpl in Heq; rewrite Heq...
  - simpl.
    replace (negb (In_nat_bool a l)) with false...
    symmetry.
    apply negb_false_iff.
    apply cond_In_nat_bool.
    split with (k0 , k1).
    split.
    + simpl in Hlt1; lia.
    + simpl in Heq; rewrite Heq...
  - simpl.
    case (In_nat_bool a l)...
    apply IHl with k0 k1 k2...
    + simpl in Hlt1; lia.
    + simpl in Hlt2; lia.
    + intros H; apply nHeq; rewrite H...
Qed.

Lemma cond_all_distinct_false_inv : forall l k0,
    all_distinct l = false ->
    {' (k1 , k2) : _ & prod (k1 < length l) (prod (k2 < length l) (prod (k1 <> k2) (nth l k0 k1 = nth l k0 k2)))}.
Proof with try reflexivity; try assumption.
  induction l; intros k0 nHalt; try now inversion nHalt.
  apply andb_false_elim in nHalt as [Hin | nHalt].
  - apply negb_false_iff in Hin.
    apply cond_In_nat_bool_inv with _ _ k0 in Hin as (k2 & (Hlt & Heq)).
    split with (0 , S k2).
    split; [ | split ; [ | split]].
    + simpl; lia.
    + simpl; lia.
    + intros H; inversion H.
    + simpl; rewrite Heq...
  - destruct (IHl k0 nHalt) as ((k1 & k2) & (Hlt1 & (Hlt2 & (nHeq & Heq)))).
    split with (S k1 , S k2).
    split; [ | split ; [ | split]].
    + simpl; lia.
    + simpl; lia.
    + intros H; inversion H; apply nHeq...
    + simpl; rewrite Heq...
Qed.

Lemma all_distinct_app_commu : forall l1 l2,
    all_distinct (l1 ++ l2) = all_distinct (l2 ++ l1).
Proof with try reflexivity; try assumption.
  induction l1; intros l2.
  - rewrite app_nil_r...
  - simpl.
    induction l2.
    + rewrite app_nil_r...
    + simpl.
      rewrite<- IHl2.
      case_eq (In_nat_bool a (l1 ++ a0 :: l2)) ; intros Hin.
      * apply In_nat_bool_middle_true in Hin.
        rewrite In_nat_bool_app_commu.
        simpl.
        case_eq (a0 =? a); intros Heq...
        replace (In_nat_bool a (l1 ++ l2)) with true.
        2:{ rewrite Nat.eqb_sym in Heq.
            rewrite Heq in Hin.
            rewrite<- Hin... }
        case (In_nat_bool a0 (l1 ++ l2))...
      * apply In_nat_bool_middle_false in Hin as (nHeq & nHin).
        rewrite nHin.
        rewrite (IHl1 (a0 :: l2)).
        simpl.
        rewrite<- (IHl1 l2).
        rewrite (In_nat_bool_app_commu _ (a :: l1)).
        simpl.
        rewrite Nat.eqb_sym.
        rewrite nHeq.
        rewrite In_nat_bool_app_commu...
Qed.

Lemma all_distinct_left : forall la lb k,
    all_distinct (la ++ k :: lb) = true ->
    In_nat_bool k la = false.
Proof with try reflexivity; try assumption.
  induction la; intros lb k Had...
  apply andb_prop in Had as (nHin & Had).  
  apply orb_false_iff.
  split.
  - apply negb_true_iff in nHin.
    rewrite Nat.eqb_sym.
    destruct (In_nat_bool_middle_false _ _ _ _ nHin)...
  - apply IHla with lb...
Qed.    

Lemma all_distinct_right : forall la lb k,
    all_distinct (la ++ k :: lb) = true ->
    In_nat_bool k lb = false.
Proof with try reflexivity; try assumption.
  induction la; intros lb k Had.
  - apply andb_prop in Had as (nHin & Had).
    apply negb_true_iff in nHin...
  - apply andb_prop in Had as (_ & Had).
    apply IHla...    
Qed.

Lemma all_distinct_app : forall la lb k,
    all_lt la k = true ->
    all_distinct la = true ->
    all_distinct lb = true ->
    all_distinct (la ++ incr_all lb k) = true.
Proof with try reflexivity; try assumption.
  induction la; intros lb k Hal Hada Hadb.
  - simpl; rewrite<- all_distinct_incr_all...
  - simpl.
    simpl in Hada.
    apply andb_true_iff in Hada as (nHin & Hada).
    simpl in Hal.
    apply andb_true_iff in Hal as (Hlt & Hal).
    apply andb_true_intro.
    split.
    + apply negb_true_iff.
      rewrite In_nat_bool_app.
      apply orb_false_intro.
      * apply negb_true_iff...
      * apply negb_In_incr_all.
        apply Nat.ltb_lt...
    + apply IHla...
Qed.

Lemma all_distinct_Perm : forall l l',
    Permutation l l' ->
    all_distinct l = all_distinct l'.
Proof with try assumption; try reflexivity.
  intros l l' Hp.
  induction Hp...
  - unfold all_distinct; fold all_distinct.
    rewrite IHHp.
    rewrite In_nat_bool_Perm with _ l' _...
  - simpl.
    rewrite 2 negb_orb.
    case_eq (y =? x); intro H.
    + replace (x =? y) with true...
      rewrite Nat.eqb_sym.
      rewrite H...
    + replace (x =? y) with false.
      2:{ rewrite Nat.eqb_sym.
          rewrite H... }
      case (In_nat_bool y l); case (In_nat_bool x l)...
  - transitivity (all_distinct l')...
Qed.

(** ** shift *)
Fixpoint shift l k :=
  match l with
  | nil => nil
  | n :: l => if n <? k then (n :: shift l k) else ((S n) :: shift l k)
  end.

Lemma shift_ge : forall l k n,
    k <=? n = true ->
    shift (n :: l) k = (S n) :: (shift l k).
Proof with try reflexivity; try assumption.
  intros l k n Hge.
  simpl.
  apply Nat.leb_le in Hge.
  replace (n <? k) with false...
  symmetry.
  apply Nat.ltb_nlt.
  lia.
Qed.
  
Lemma shift_In_nat_bool_lt : forall l n k,
    n <? k = true ->
    In_nat_bool n (shift l k) = In_nat_bool n l.
Proof with try reflexivity; try assumption.
  intros l; induction l; intros n k Hlt...
  simpl.
  case_eq (a <? k); intros Hlt'.
  - simpl.
    case (n =? a)...
    rewrite IHl...
  - simpl.
    rewrite IHl...
    apply Nat.ltb_lt in Hlt.
    apply Nat.ltb_nlt in Hlt'.
    replace (n =? a) with false.
    2:{ symmetry.
        apply Nat.eqb_neq.
        lia. }
    replace (n =? S a) with false...
    symmetry.
    apply Nat.eqb_neq.
    lia.
Qed.
  
Lemma shift_In_nat_bool_ge : forall l n k,
    k <=? n = true ->
    In_nat_bool (S n) (shift l k) = In_nat_bool n l.
Proof with try reflexivity; try assumption.
  intros l; induction l; intros n k Hge...
  simpl.
  case_eq (a <? k); intros Hlt.
  - simpl.
    change (match a with
            | 0 => false
            | S m' => n =? m'
            end) with (S n =? a).
    rewrite IHl...
    apply Nat.ltb_lt in Hlt.
    apply Nat.leb_le in Hge.
    replace (S n =? a) with false.
    2:{ symmetry.
        apply Nat.eqb_neq.
        lia. }
    replace (n =? a) with false...
    symmetry.
    apply Nat.eqb_neq.
    lia.
  - simpl.
    rewrite IHl...
Qed.

Lemma shift_In_nat_bool_eq : forall l k,
    In_nat_bool (S k) (shift l k) = In_nat_bool k l.
Proof with try reflexivity; try assumption.
  induction l; intro k...
  simpl.
  case_eq (a <? k); intros Hlt.
  - simpl.
    change ( match a with
             | 0 => false
             | S m' => k =? m'
             end) with (S k =? a).
    rewrite IHl.
    apply Nat.ltb_lt in Hlt.
    replace (S k =? a) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (k =? a) with false by (symmetry; apply Nat.eqb_neq; lia)...
  - simpl; rewrite IHl...
Qed.  

Lemma shift_length : forall l n,
    length (shift l n) = length l.
Proof with try reflexivity; try assumption.
  intros l n; induction l...
  simpl; case (a <? n); simpl; rewrite IHl...
Qed.

Lemma nth_shift_ge : forall l n k0 k,
    In_nat_bool n l = false ->
    k < length l ->
    n <= nth l k0 k ->
    nth (shift l n) k0 k = S (nth l k0 k).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin Hlen Hge.
  - inversion Hlen.
  - destruct k.
    + simpl.
      case_eq (a <? n); intros Hlt...
      apply Nat.ltb_lt in Hlt.
      simpl in Hge.
      exfalso.
      lia.
    + simpl.
      case_eq (a <? n); intros Hlt.
      * apply orb_false_elim in nHin as (_ & nHin).
        apply Lt.lt_S_n in Hlen.
        refine (IHl _ _ _ nHin Hlen Hge).
      * case_eq (a =? n); intros Heq.
        -- simpl in nHin.
           replace (n =? a) with true in nHin; try now inversion nHin.
           symmetry.
           rewrite Nat.eqb_sym...
        -- apply orb_false_elim in nHin as (_ & nHin).
           apply Lt.lt_S_n in Hlen.
           refine (IHl _ _ _ nHin Hlen Hge).
Qed.  

Lemma nth_shift_lt : forall l n k0 k,
    In_nat_bool n l = false ->
    k < length l ->
    nth l k0 k < n ->
    nth (shift l n) k0 k = (nth l k0 k).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin Hlen Hlt.
  - inversion Hlen.
  - destruct k.
    + simpl.
      case_eq (a <? n); intros Hlt'...
      simpl in Hlt.
      apply Nat.ltb_nlt in Hlt'.
      exfalso; lia.
    + simpl.
      case_eq (a <? n); intros Hlt'.
      * apply orb_false_elim in nHin as (_ & nHin).
        apply Lt.lt_S_n in Hlen.
        refine (IHl _ _ _ nHin Hlen Hlt).
      * case_eq (a =? n); intros Heq.
        -- simpl in nHin.
           replace (n =? a) with true in nHin; try now inversion nHin.
           symmetry.
           rewrite Nat.eqb_sym...
        -- apply orb_false_elim in nHin as (_ & nHin).
           apply Lt.lt_S_n in Hlen.
           refine (IHl _ _ _ nHin Hlen Hlt).
Qed.

Lemma le_nth_shift : forall l n k0 k,
    nth l k0 k <= nth (shift l n) k0 k.
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k...
  destruct k ; simpl.
  - case (a <? n); simpl; lia.
  - case (a <? n); simpl; apply IHl.  
Qed.

Lemma nth_ge_shift : forall l n k0 k,
    k < length l ->
    n <= nth (shift l n) k0 k ->
    nth (shift l n) k0 k = S (nth l k0 k).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k Hlen Hgt.
  - inversion Hlen.
  - simpl in Hgt.
    simpl.
    destruct k.
    + case_eq (a <? n); intros Hlt; rewrite Hlt in Hgt...
      apply Nat.ltb_lt in Hlt.
      simpl in Hgt.
      lia.
    + case_eq (a <? n); intros Hlt; rewrite Hlt in Hgt; apply Lt.lt_S_n in Hlen; refine (IHl _ _ _ Hlen Hgt).
Qed.  

Lemma nth_lt_shift : forall l n k0 k,
    k < length l ->
    nth (shift l n) k0 k < n ->
    nth (shift l n) k0 k = (nth l k0 k).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k Hlen Hlt.
  - inversion Hlen.
  - simpl.
    simpl in Hlt.
    destruct k.
    + case_eq (a <? n); intros Hlt'; rewrite Hlt' in Hlt...
      simpl in Hlt.
      apply Nat.ltb_nlt in Hlt'.
      lia.
    + case_eq (a <? n); intros Hlt'; rewrite Hlt' in Hlt; apply Lt.lt_S_n in Hlen; refine (IHl _ _ _ Hlen Hlt).
Qed.

Lemma shift_all_lt : forall l n k,
    k <=? n = true ->
    all_lt l n = all_lt (shift l k) (S n).
Proof with try reflexivity; try assumption.
  intros l n k Hleq; induction l...
  simpl.
  case_eq (a <? k); intros Hlt; simpl; rewrite IHl...
  apply Nat.leb_le in Hleq.
  apply Nat.ltb_lt in Hlt.
  replace (a <? n) with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (a <? S n) with true by (symmetry; apply Nat.ltb_lt; lia)...
Qed.

Lemma shift_keep_all_distinct : forall l k,
    all_distinct l = true ->
    all_distinct (shift l k) = true.
Proof with try reflexivity; try assumption.
  induction l; intros k Hal...
  simpl in Hal |- *.
  case_eq (a <? k); intros Hlt; simpl; splitb.
  - apply andb_prop in Hal as (nHin & _).
    rewrite shift_In_nat_bool_lt...
  - apply andb_prop in Hal as (_ & Hal).
    apply IHl...
  - apply andb_prop in Hal as (nHin & _).
    rewrite shift_In_nat_bool_ge...
    apply Nat.leb_le.
    apply Nat.ltb_nlt in Hlt.
    lia.
  - apply andb_prop in Hal as (_ & Hal).
    apply IHl...
Qed.

Lemma app_nat_fun_shift {A} : forall la lb (a : A) p
                                     (H : length (la ++ lb) <> 0)
                                     (Halt : all_lt p (length (la ++ lb)) = true),
    app_nat_fun (la ++ a :: lb) (shift p (length la)) = app_nat_fun (la ++ lb) p.
Proof with try reflexivity; try assumption.
  intros la lb a p;
    revert la lb a;
    induction p;
    intros la lb b H Halt.
  - destruct la; destruct lb...
  - destruct la; [destruct lb | ].
    + exfalso.
      apply H...
    + rewrite ? app_nil_l.
      change (length nil) with 0.
      unfold app_nat_fun.
      change (shift (a :: p) 0) with ((S a) :: shift p 0).
      rewrite 2 map_cons.
      change (nth (b :: a0 :: lb) b (S a)) with (nth (a0 :: lb) b a).
      specialize (IHp nil (a0 :: lb) b).
      rewrite 2 app_nil_l in IHp.
      unfold app_nat_fun in IHp.
      change (length nil) with 0 in IHp.
      rewrite IHp.
      * replace (nth (a0 :: lb) b a) with (nth (a0 :: lb) a0 a)...
        apply nth_correct.
        apply andb_prop in Halt as (Hlt & _).
        apply Nat.ltb_lt in Hlt...
      * intros Heq; inversion Heq.
      * apply andb_prop in Halt as (_ & Halt)...
    + change ((a0 :: la) ++ b :: lb) with (a0 :: la ++ b :: lb).
      change ((a0 :: la) ++ lb) with (a0 :: la ++ lb).
      unfold app_nat_fun.
      specialize (IHp (a0 :: la) lb b).
      remember (length (a0 :: la)) as n.
      apply andb_prop in Halt as (Hlt & Halt).
      change ((fix all_lt (l : list nat) (n : nat) {struct l} : bool :=
            match l with
            | nil => true
            | k :: l0 => (k <? n) && all_lt l0 n
            end) p (length ((a0 :: la) ++ lb))) with (all_lt p (length ((a0 :: la) ++ lb))) in Halt.
      case_eq (a <? n); intros Hltan.
      * replace (shift (a :: p) n) with (a :: shift p n).
        2:{ simpl.
            rewrite Hltan... }
        rewrite 2 map_cons.
        rewrite Heqn in Hltan.
        apply Nat.ltb_lt in Hltan.
        change (a0 :: la ++ b :: lb) with ((a0 :: la) ++ b :: lb).
        rewrite (nth_left (a0 :: la) (b :: lb) a0 a Hltan).
        change (a0 :: la ++ lb) with ((a0 :: la) ++ lb).
        rewrite (nth_left (a0 :: la) lb a0 a Hltan).
        change (map (fun x : nat => nth ((a0 :: la) ++ lb) a0 x) p) with (app_nat_fun ((a0 :: la) ++ lb) p).
        change (map (fun x : nat => nth ((a0 :: la) ++ b :: lb) a0 x) (shift p n)) with
            (app_nat_fun ((a0 :: la) ++ b :: lb) (shift p n)).
        rewrite IHp...
      * destruct a.
        { destruct n.
          - inversion Heqn.
          - apply Nat.ltb_nlt in Hltan.
            lia. }
        replace (shift (S a :: p) n) with (S (S a) :: shift p n).
        2:{ simpl.
            rewrite Hltan... }
        rewrite 2 map_cons.
        change (map (fun x : nat => nth (a0 :: la ++ lb) a0 x) p) with (app_nat_fun ((a0 :: la) ++ lb) p).
        change (map (fun x : nat => nth (a0 :: la ++ b :: lb) a0 x) (shift p n)) with (app_nat_fun ((a0 :: la) ++ b :: lb) (shift p n)).
        rewrite IHp...
        replace (nth (a0 :: la ++ b :: lb) a0 (S (S a))) with (nth (a0 :: la ++ lb) a0 (S a))...
        rewrite Heqn in Hltan.
        clear - Hltan.
        apply Nat.ltb_nlt in Hltan.
        change (a0 :: la ++ lb) with ((a0 :: la) ++ lb).
        change (a0 :: la ++ b :: lb) with ((a0 :: la) ++ b :: lb).
        remember (a0 :: la).
        clear Heql la.
        revert a Hltan.
        induction l; intros n nHlt...
        simpl in nHlt.
        simpl.
        destruct n.
        { destruct l...
          simpl in nHlt.
          exfalso.
          apply nHlt.
          lia. }
        apply IHl; try lia.
Qed.

Lemma shift_incr_all : forall l n,
    shift (incr_all l (S n)) n = incr_all l (S (S n)).
Proof with try reflexivity; try assumption.
  induction l...
  simpl.
  intro n.
  replace (S (n + a) <? n ) with false.
  2:{ symmetry.
      apply Nat.ltb_nlt.
      lia. }
  rewrite (IHl n).
  destruct n...
Qed.

Lemma shift_app : forall l1 l2 n,
    shift (l1 ++ l2) n = shift l1 n ++ shift l2 n.
Proof with try reflexivity; try assumption.
  induction l1; intros l2 n...
  simpl.
  rewrite (IHl1 l2 n).
  case (a <? n)...
Qed.

Lemma shift_if_all_lt : forall l n,
    all_lt l n = true ->
    shift l n = l.
Proof with try reflexivity; try assumption.
  induction l; intros n Hal...
  apply andb_prop in Hal as (Hlt & Hal).
  simpl.
  rewrite Hlt.
  rewrite IHl...
Qed.

Lemma In_nat_bool_shift_false : forall l f n0 n,
    all_lt f (pred (length l)) = true ->
    n < length l ->
    all_distinct l = true ->
    In_nat_bool (nth l n0 n) (app_nat_fun l (shift f n)) = false.
Proof with try reflexivity; try assumption.
  intros l f n0 n Hal Hlen Had.
  destruct l; try now inversion Hlen.
  induction f...
  unfold shift.
  change ((fix shift (l0 : list nat) (k : nat) {struct l0} : 
             list nat :=
             match l0 with
             | nil => nil
             | n2 :: l1 =>
               if n2 <? k then n2 :: shift l1 k else S n2 :: shift l1 k
             end) f n)
    with (shift f n).
  simpl in Hal.
  apply andb_prop in Hal as (Hlt & Hal).
  case_eq (a <? n); intros Hlt'.
  - app_nat_fun_unfold l (shift f n) n1 a.
    apply orb_false_iff.
    split ; [ | apply IHf]...
    case_eq (nth (n1 :: l) n0 n =? nth (n1 :: l) n1 a); intros Heq...
    exfalso.
    apply Nat.ltb_lt in Hlt'.
    apply (Nat.lt_neq a n)...
    symmetry.
    apply Nat.eqb_eq in Heq.
    replace (nth (n1 :: l) n1 a) with (nth (n1 :: l) n0 a) in Heq.
    2:{ apply nth_correct.
        simpl.
        apply Nat.ltb_lt in Hlt.
        lia. }
    apply cond_all_distinct_inv with (n1 :: l) n0...
    simpl.
    apply Nat.ltb_lt in Hlt.
    lia.
  - app_nat_fun_unfold l (shift f n) n1 (S a).
    apply orb_false_iff.
    split ; [ | apply IHf]...
    assert (n <> S a).
    { apply Nat.ltb_nlt in Hlt'.
      lia. }
    replace (nth (n1 :: l) n1 (S a)) with (nth (n1 :: l) n0 (S a)).
    2:{ apply nth_correct.
        simpl.
        apply Nat.ltb_lt... }
    case_eq (nth (n1 :: l) n0 n =? nth (n1 :: l) n0 (S a)); intros Heq...
    exfalso.
    apply H.
    apply Nat.eqb_eq in Heq.
    apply cond_all_distinct_inv with (n1 :: l) n0...
    simpl; apply Nat.ltb_lt...
Qed.
  
(** ** downshift *)
Fixpoint downshift l k :=
  match l with
  | nil => nil
  | n :: l => if n <? k then (n :: downshift l k) else (if n =? k then downshift l k else (pred n) :: downshift l k)
  end.

Definition down_nat n m := if n <? m then n else pred n.

Lemma downshift_eq : forall l k, downshift (k :: l) k = downshift l k.
Proof with try reflexivity; try assumption.
  intro l; intros k.
  simpl.
  replace (k <? k) with false.
  2:{ symmetry.
      apply Nat.ltb_nlt.
      lia. }
  replace (k =? k) with true...
  symmetry.
  apply Nat.eqb_eq...
Qed.

Lemma downshift_gt : forall l k n,
    k <? n = true ->
    downshift (n :: l) k = (pred n) :: (downshift l k).
Proof with try reflexivity; try assumption.
  intros l k n Hlt.
  simpl.
      apply Nat.ltb_lt in Hlt.
  replace (n <? k) with false.
  2:{ symmetry.
      apply Nat.ltb_nlt.
      lia. }
  replace (n =? k) with false...
  symmetry.
  apply Nat.eqb_neq.
  lia.
Qed.
  
Lemma downshift_In_nat_bool_lt : forall l n k,
    n <? k = true ->
    In_nat_bool n (downshift l k) = In_nat_bool n l.
Proof with try reflexivity; try assumption.
  intros l; induction l; intros n k Hlt...
  destruct (Compare_dec.lt_eq_lt_dec a k) as [[H1 | H2] | H3].
  - apply Nat.ltb_lt in H1.
    simpl; rewrite H1.
    simpl; rewrite (IHl n k Hlt)...
  - subst.
    rewrite (downshift_eq l k).
    assert (k <> n).
    { apply Nat.ltb_lt in Hlt.
      lia. }
    rewrite (In_nat_bool_neq _ _ _ H).
    apply IHl...
  - apply Nat.ltb_lt in H3.
    rewrite (downshift_gt _ _ _ H3).
    destruct a.
    + exfalso.
      apply Nat.ltb_lt in H3.
      lia.
    + simpl.
      replace (n =? a) with false.
      2:{ symmetry.
          apply Nat.eqb_neq.
          apply Nat.ltb_lt in Hlt.
          apply Nat.ltb_lt in H3.
          lia. }
      replace (n =? S a) with false.
      2:{ symmetry.
          apply Nat.eqb_neq.
          apply Nat.ltb_lt in Hlt.
          apply Nat.ltb_lt in H3.
          lia. }
      apply IHl...      
Qed.
  
Lemma downshift_In_nat_bool_gt : forall l n k,
    k <? n = true ->
    In_nat_bool (pred n) (downshift l k) = In_nat_bool n l.
Proof with try reflexivity; try assumption.
  intros l; induction l; intros n k Hlt...
  destruct (Compare_dec.lt_eq_lt_dec a k) as [[H1 | H2] | H3].
  - apply Nat.ltb_lt in H1.
    simpl; rewrite H1.
    simpl; rewrite (IHl n k Hlt).
    apply Nat.ltb_lt in Hlt.
    apply Nat.ltb_lt in H1.
    replace (pred n =? a) with false.
    2:{ symmetry.
        apply Nat.eqb_neq.
        lia. }
    replace (n =? a) with false...
    symmetry.
    apply Nat.eqb_neq...
    lia.
  - subst.
    rewrite (downshift_eq l k).
    assert (k <> n).
    { apply Nat.ltb_lt in Hlt.
      lia. }
    rewrite (In_nat_bool_neq _ _ _ H).
    apply IHl...
  - apply Nat.ltb_lt in H3.
    apply Nat.ltb_lt in Hlt.
    rewrite (downshift_gt _ _ _ H3).
    apply Nat.ltb_lt in H3.
    destruct n; destruct a; try (exfalso; lia).
    simpl.
    apply Nat.ltb_lt in Hlt.
    rewrite<- (IHl (S n) k Hlt)...
Qed.

Lemma downshift_In_nat_bool_eq : forall l k,
    In_nat_bool k (downshift l k) = In_nat_bool (S k) l.
Proof with try reflexivity; try assumption.
  induction l; intro k...
  destruct (Compare_dec.lt_eq_lt_dec a k) as [[H1 | H2] | H3].
  - simpl.
    apply Nat.ltb_lt in H1.
    rewrite H1.
    change (match a with
            | 0 => false
            | S m' => k =? m'
            end) with (S k =? a).
    apply Nat.ltb_lt in H1.
    replace (S k =? a) with false.
    2:{ symmetry.
        apply Nat.eqb_neq.
        lia. }
    simpl.
    replace (k =? a) with false.
    2:{ symmetry.
        apply Nat.eqb_neq.
        lia. }
    refine (IHl k).
  - subst.
    rewrite downshift_eq.
    simpl.
    change ( match k with
              | 0 => false
              | S m' => k =? m'
             end) with (S k =? k).
    replace (S k =? k) with false.
    2:{ symmetry.
        apply Nat.eqb_neq.
        lia. }
    refine (IHl _).
  - simpl.
    change ( match a with
              | 0 => false
              | S m' => k =? m'
             end) with (S k =? a).
    replace (a <? k) with false.
    2:{ symmetry.
        apply Nat.ltb_nlt.
        lia. }
    replace (a =? k) with false.
    2:{ symmetry.
        apply Nat.eqb_neq.
        lia. }
    destruct a ; [exfalso; lia |].
    case_eq (k =? a); intro Heq.
    + apply Nat.eqb_eq in Heq.
      subst.
      simpl.
      replace (a =? a) with true...
      symmetry; apply Nat.eqb_eq...
    + simpl.
      rewrite Heq.
      refine (IHl k).
Qed.  

Lemma downshift_length : forall l n,
    In_nat_bool n l = false ->
    length (downshift l n) = length l.
Proof with try reflexivity; try assumption.
  intros l n nHin; induction l...
  simpl in nHin.
  apply orb_false_iff in nHin as (nHeq & nHin).
  rewrite Nat.eqb_sym in nHeq.
  simpl.
  case (a <? n); simpl; try rewrite (IHl nHin)...
  rewrite nHeq; simpl; rewrite IHl...
Qed.

Lemma nth_downshift_gt : forall l n k0 k,
    In_nat_bool n l = false ->
    k < length l ->
    n < nth l k0 k ->
    nth (downshift l n) k0 k = pred (nth l k0 k).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin Hlen Hgt.
  - inversion Hlen.
  - destruct k.
    + simpl.
      case_eq (a <? n); intros Hlt.
      * apply Nat.ltb_lt in Hlt.
        simpl in Hgt.
        exfalso.
        lia.
      * case_eq (a =? n); intros Heq...
        apply Nat.eqb_eq in Heq.
        simpl in Hgt.
        lia.
    + simpl.
      case_eq (a <? n); intros Hlt.
      * apply orb_false_elim in nHin as (_ & nHin).
        apply Lt.lt_S_n in Hlen.
        refine (IHl _ _ _ nHin Hlen Hgt).
      * case_eq (a =? n); intros Heq.
        -- simpl in nHin.
           replace (n =? a) with true in nHin; try now inversion nHin.
           symmetry.
           rewrite Nat.eqb_sym...
        -- apply orb_false_elim in nHin as (_ & nHin).
           apply Lt.lt_S_n in Hlen.
           refine (IHl _ _ _ nHin Hlen Hgt).
Qed.  

Lemma nth_downshift_lt : forall l n k0 k,
    In_nat_bool n l = false ->
    k < length l ->
    nth l k0 k < n ->
    nth (downshift l n) k0 k = (nth l k0 k).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin Hlen Hlt.
  - inversion Hlen.
  - destruct k.
    + simpl.
      case_eq (a <? n); intros Hlt'...
      case_eq (a =? n); intros Heq.
      * apply Nat.eqb_eq in Heq.
        simpl in Hlt.
        lia.
      * apply Nat.eqb_neq in Heq.
        apply Nat.ltb_nlt in Hlt'.
        simpl in Hlt.
        lia.
    + simpl.
      case_eq (a <? n); intros Hlt'.
      * apply orb_false_elim in nHin as (_ & nHin).
        apply Lt.lt_S_n in Hlen.
        refine (IHl _ _ _ nHin Hlen Hlt).
      * case_eq (a =? n); intros Heq.
        -- simpl in nHin.
           replace (n =? a) with true in nHin; try now inversion nHin.
           symmetry.
           rewrite Nat.eqb_sym...
        -- apply orb_false_elim in nHin as (_ & nHin).
           apply Lt.lt_S_n in Hlen.
           refine (IHl _ _ _ nHin Hlen Hlt).
Qed.

Lemma le_nth_downshift : forall l n k0 k,
    In_nat_bool n l = false ->
    nth (downshift l n) k0 k <= nth l k0 k.
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin...
  destruct (orb_false_elim _ _ nHin) as (_ & nHin').
  simpl.
  case (a <? n) ; [ | case_eq (a =? n); intros Heq; [simpl in nHin; rewrite Nat.eqb_sym in Heq; rewrite Heq in nHin; inversion nHin | ]]; destruct k; try apply IHl...
  - apply Nat.le_pred_l.
Qed.

Lemma nth_ge_downshift : forall l n k0 k,
    In_nat_bool n l = false ->
    k < length l ->
    n <= nth (downshift l n) k0 k ->
    nth (downshift l n) k0 k = pred (nth l k0 k).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin Hlen Hgt.
  - inversion Hlen.
  - simpl in Hgt.
    simpl.
    destruct k.
    + case_eq (a <? n); intros Hlt; rewrite Hlt in Hgt.
      * apply Nat.ltb_lt in Hlt.
        simpl in Hgt.
        lia.
      * case_eq (a =? n); intros Heq; rewrite Heq in Hgt...
        unfold In_nat_bool in nHin.
        rewrite Nat.eqb_sym in Heq.
        rewrite Heq in nHin.
        inversion nHin.
    + case_eq (a <? n); intros Hlt; rewrite Hlt in Hgt.
      * apply orb_false_elim in nHin as (_ & nHin).
        apply Lt.lt_S_n in Hlen.
        refine (IHl _ _ _ nHin Hlen Hgt).
      * case_eq (a =? n); intros Heq; rewrite Heq in Hgt.
        -- simpl in nHin.
           rewrite Nat.eqb_sym in nHin.
           rewrite Heq in nHin.
           inversion nHin.
        -- apply orb_false_elim in nHin as (_ & nHin).
           apply Lt.lt_S_n in Hlen.
           refine (IHl _ _ _ nHin Hlen Hgt).
Qed.  

Lemma nth_lt_downshift : forall l n k0 k,
    In_nat_bool n l = false ->
    k < length l ->
    nth (downshift l n) k0 k < n ->
    nth (downshift l n) k0 k = (nth l k0 k).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin Hlen Hlt.
  - inversion Hlen.
  - simpl.
    simpl in Hlt.
    destruct k.
    + case_eq (a <? n); intros Hlt'; rewrite Hlt' in Hlt...
      case_eq (a =? n); intros Heq; rewrite Heq in Hlt.
      * simpl in nHin.
        rewrite Nat.eqb_sym in nHin.
        rewrite Heq in nHin.
        inversion nHin.
      * apply Nat.eqb_neq in Heq.
        apply Nat.ltb_nlt in Hlt'.
        simpl in Hlt.
        lia.
    + case_eq (a <? n); intros Hlt'; rewrite Hlt' in Hlt.
      * apply orb_false_elim in nHin as (_ & nHin).
        apply Lt.lt_S_n in Hlen.
        refine (IHl _ _ _ nHin Hlen Hlt).
      * case_eq (a =? n); intros Heq; rewrite Heq in Hlt.
        -- simpl in nHin.
           replace (n =? a) with true in nHin; try now inversion nHin.
           symmetry.
           rewrite Nat.eqb_sym...
        -- apply orb_false_elim in nHin as (_ & nHin).
           apply Lt.lt_S_n in Hlen.
           refine (IHl _ _ _ nHin Hlen Hlt).
Qed.

Lemma downshift_all_lt : forall l n k,
    k <=? n = true ->
    all_lt l (S n) = all_lt (downshift l k) n.
Proof with try reflexivity; try assumption.
  intros l n k Hleq; induction l...
  destruct (Compare_dec.lt_eq_lt_dec a k) as [[H1 | H2] | H3].
  - apply Nat.ltb_lt in H1.
    simpl; rewrite H1.
    simpl.
    apply Nat.ltb_lt in H1.
    apply Nat.leb_le in Hleq.
    replace (a <? S n) with true.
    2:{ symmetry.
        apply Nat.ltb_lt.
        lia. }
    replace (a <? n) with true...
    symmetry.
    apply Nat.ltb_lt.
    lia.
  - subst.
    rewrite downshift_eq.
    simpl.
    rewrite IHl.
    replace (k <? S n) with true...
  - apply Nat.ltb_lt in H3.
    rewrite downshift_gt...
    destruct a; simpl.
    + apply Nat.ltb_lt in H3; lia.
    + change (S a <? S n) with (a <? n).
      rewrite IHl...
Qed.

Lemma downshift_keep_all_distinct : forall l k,
    all_distinct l = true ->
    all_distinct (downshift l k) = true.
Proof with try reflexivity; try assumption.
  induction l; intros k Hal...
  destruct (Compare_dec.lt_eq_lt_dec a k) as [[H1 | H2] | H3].
  - apply Nat.ltb_lt in H1.
    simpl; rewrite H1.
    apply andb_prop in Hal as (nHin & Hal).
    splitb.
    + rewrite downshift_In_nat_bool_lt...
    + refine (IHl k Hal).
  - subst.
    rewrite downshift_eq.
    apply andb_prop in Hal as (nHin & Hal).
    refine (IHl k Hal).
  - apply andb_prop in Hal as (nHin & Hal).
    specialize (IHl k Hal).
    clear Hal.
    rewrite downshift_gt.
    2:{ apply Nat.ltb_lt... }
    splitb...
    rewrite downshift_In_nat_bool_gt by (apply Nat.ltb_lt; apply H3)...
Qed.

Lemma app_nat_fun_downshift {A} : forall la lb (a : A) p
                                         (nHin : In_nat_bool (length la) p = false)
                                         (Halt : all_lt p (S (length (la ++ lb))) = true),
    app_nat_fun (la ++ a :: lb) p = app_nat_fun (la ++ lb) (downshift p (length la)).
Proof with try reflexivity; try assumption.
  intros la lb a p;
    revert la lb a;
    induction p;
    intros la lb b nHin Halt.
  - destruct la; destruct lb...
  - destruct la; [destruct lb | ].
    + destruct a; try now inversion nHin.
    + rewrite ? app_nil_l.
      change (length nil) with 0.
      unfold app_nat_fun.
      destruct a ; try now inversion nHin.
      change (downshift ((S a) :: p) 0) with (a :: downshift p 0).
      rewrite 2 map_cons.
      change (nth (b :: a0 :: lb) b (S a)) with (nth (a0 :: lb) b a).
      specialize (IHp nil (a0 :: lb) b).
      rewrite 2 app_nil_l in IHp.
      unfold app_nat_fun in IHp.
      change (length nil) with 0 in IHp.
      rewrite IHp.
      * replace (nth (a0 :: lb) b a) with (nth (a0 :: lb) a0 a)...
        apply nth_correct.
        apply andb_prop in Halt as (Hlt & _).
        apply Nat.ltb_lt in Hlt.
        rewrite app_nil_l in Hlt; lia.
      * apply orb_false_iff in nHin as (_ & H)...
      * apply andb_prop in Halt as (_ & Halt)...
    + change ((a0 :: la) ++ b :: lb) with (a0 :: la ++ b :: lb).
      change ((a0 :: la) ++ lb) with (a0 :: la ++ lb).
      unfold app_nat_fun.
      specialize (IHp (a0 :: la) lb b).
      remember (length (a0 :: la)) as n.
      apply orb_false_iff in nHin as (nHeq & nHin).
      change ((fix In_nat_bool (n : nat) (l : list nat) {struct l} : bool :=
            match l with
            | nil => false
            | k :: l0 => (n =? k) || In_nat_bool n l0
            end) n p) with (In_nat_bool n p) in nHin.
      apply andb_prop in Halt as (Hlt & Halt).
      change ((fix all_lt (l : list nat) (n : nat) {struct l} : bool :=
            match l with
            | nil => true
            | k :: l0 => (k <? n) && all_lt l0 n
            end) p (S (length ((a0 :: la) ++ lb)))) with (all_lt p (S (length ((a0 :: la) ++ lb)))) in Halt.
      case_eq (a <? n); intros Hltan.
      * replace (downshift (a :: p) n) with (a :: downshift p n).
        2:{ simpl.
            rewrite Hltan... }
        rewrite 2 map_cons.
        rewrite Heqn in Hltan.
        apply Nat.ltb_lt in Hltan.
        change (a0 :: la ++ b :: lb) with ((a0 :: la) ++ b :: lb).
        rewrite (nth_left (a0 :: la) (b :: lb) a0 a Hltan).
        change (a0 :: la ++ lb) with ((a0 :: la) ++ lb).
        rewrite (nth_left (a0 :: la) lb a0 a Hltan).
        change (map (fun x : nat => nth ((a0 :: la) ++ b :: lb) a0 x) p) with (app_nat_fun ((a0 :: la) ++ b :: lb) p).
        rewrite IHp...
      * rewrite Nat.eqb_sym in nHeq.
        destruct a.
        { destruct n.
          - apply Nat.eqb_neq in nHeq.
            exfalso; apply nHeq...
          - apply Nat.ltb_nlt in Hltan.
            lia. }
        replace (downshift (S a :: p) n) with (a :: downshift p n).
        2:{ simpl.
            rewrite Hltan.
            simpl in nHeq;rewrite nHeq... }
        rewrite 2 map_cons.
        change (map (fun x : nat => nth (a0 :: la ++ b :: lb) a0 x) p) with (app_nat_fun ((a0 :: la) ++ b :: lb) p).

        change (map (fun x : nat => nth (a0 :: la ++ lb) a0 x) (downshift p n)) with (app_nat_fun ((a0 :: la) ++ lb) (downshift p n)).
        rewrite IHp...
        replace (nth (a0 :: la ++ b :: lb) a0 (S a)) with (nth (a0 :: la ++ lb) a0 a)...
        rewrite Heqn in Hltan, nHeq.
        clear - Hltan nHeq.
        apply Nat.eqb_neq in nHeq.
        apply Nat.ltb_nlt in Hltan.
        change (a0 :: la ++ lb) with ((a0 :: la) ++ lb).
        change (a0 :: la ++ b :: lb) with ((a0 :: la) ++ b :: lb).
        remember (a0 :: la).
        clear Heql la.
        revert a nHeq Hltan.
        induction l; intros n nHeq nHlt...
        simpl in nHeq, nHlt.
        simpl.
        destruct n.
        { destruct l; try lia. }
        apply IHl; try lia.
Qed.

Lemma downshift_incr_all : forall l n,
    downshift (incr_all l (S n)) n = incr_all l n.
Proof with try reflexivity; try assumption.
  induction l...
  simpl.
  intro n.
  replace (S (n + a) <? n ) with false.
  2:{ symmetry.
      apply Nat.ltb_nlt.
      lia. }
  rewrite (IHl n).
  destruct n...
  replace (S n + a =? n) with false...
  symmetry.
  apply Nat.eqb_neq.
  lia.  
Qed.

Lemma downshift_app : forall l1 l2 n,
    downshift (l1 ++ l2) n = downshift l1 n ++ downshift l2 n.
Proof with try reflexivity; try assumption.
  induction l1; intros l2 n...
  simpl.
  rewrite (IHl1 l2 n).
  case (a <? n)...
  case (a =? n)...
Qed.

Lemma downshift_if_all_lt : forall l n,
    all_lt l n = true ->
    downshift l n = l.
Proof with try reflexivity; try assumption.
  induction l; intros n Hal...
  apply andb_prop in Hal as (Hlt & Hal).
  simpl.
  rewrite Hlt.
  rewrite IHl...
Qed.

Lemma downshift_shift : forall l n,
    downshift (shift l n) n = l.
Proof with try reflexivity; try assumption.
  induction l; intros n...
  simpl.
  case_eq (a <? n); intros Hlt.
  - simpl.
    rewrite Hlt.
    rewrite IHl...
  - simpl.
    apply Nat.ltb_nlt in Hlt.
    replace (S a <? n) with false by (symmetry; apply Nat.ltb_nlt; lia).
    change (match n with
            | 0 => false
            | S m' => a =? m'
            end) with (S a =? n).
    case_eq (S a =? n); intros Heq; [ | rewrite IHl]...
    apply Nat.eqb_eq in Heq.
    lia.
Qed.

Lemma shift_downshift : forall l n,
    In_nat_bool n l = false ->
    shift (downshift l n) n = l.
Proof with try reflexivity; try assumption.
  induction l; intros n nHin...
  simpl in nHin; apply orb_false_iff in nHin as (nHeq & nHin).
  simpl.
  case_eq (a <? n); intros Hlt.
  - simpl; rewrite Hlt.
    rewrite IHl...
  - rewrite Nat.eqb_sym in nHeq.
    rewrite nHeq.
    destruct a; try now (destruct n; inversion nHeq).
    simpl.
    rewrite IHl...
    replace (a <? n) with false...
    symmetry.
    apply Nat.ltb_nlt.
    apply Nat.ltb_nlt in Hlt.
    apply Nat.eqb_neq in nHeq.
    lia.
Qed.

Lemma incr_all_downshift_0 : forall l,
    In_nat_bool 0 l = false ->
    incr_all (downshift l 0) 1 = l.
Proof with try reflexivity; try assumption.
  induction l; intros nHin...
  destruct a.
  { inversion nHin. }
  rewrite downshift_gt...
  simpl.
  rewrite IHl...
Qed.

Lemma downshift_nth : forall l1 l2 a0 k1 k2,
    k1 < length l1 ->
    In_nat_bool k2 l1 = false ->
    downshift ((nth l1 a0 k1) :: l2) k2 = (nth (downshift l1 k2) a0 k1 :: (downshift l2 k2)).
Proof with try reflexivity; try assumption.
  induction l1; intros l2 a0 k1 k2 Hlen nHin; try now inversion Hlen.
  destruct k1.
  - change (nth (a :: l1) a0 0) with a.
    case_eq (a <? k2); intros Hlt.
    + simpl.
      rewrite Hlt...
    + assert (k2 <? a = true) as Hgt.
      { apply Nat.ltb_lt.
        apply Nat.ltb_nlt in Hlt.
        apply orb_false_iff in nHin as (nHeq & _).
        apply Nat.eqb_neq in nHeq.
        lia. }
      rewrite 2 downshift_gt...
  - change (nth (a :: l1) a0 (S k1)) with (nth l1 a0 k1).
    replace (nth (downshift (a :: l1) k2) a0 (S k1)) with (nth (downshift l1 k2) a0 k1).
    { simpl in Hlen.
      apply Lt.lt_S_n in Hlen.
      apply orb_false_iff in nHin as (_ & nHin).
      apply IHl1... }
    case_eq (a <? k2); intros Hlt.
    + simpl.
      rewrite Hlt...
    + assert (k2 <? a = true) as Hgt.
      { apply Nat.ltb_lt.
        apply Nat.ltb_nlt in Hlt.
        apply orb_false_iff in nHin as (nHeq & _).
        apply Nat.eqb_neq in nHeq.
        lia. }
      rewrite downshift_gt...
Qed.
        
Lemma app_nat_fun_downshift_commu : forall a l f k,
    In_nat_bool k (a :: l) = false ->
    all_lt f (length (a :: l)) = true ->
    all_distinct f = true ->
    app_nat_fun (downshift (a :: l) k) f = downshift (app_nat_fun (a :: l) f) k.
Proof with try reflexivity; try assumption.
  intros a l f k nHin Hal Had.
  revert a l k nHin Hal Had; induction f; intros b l k nHin Hal Had.
  { rewrite app_nat_fun_nil... }
  case_eq (b <? k); intros Hlt.
  - assert (downshift (b :: l) k = b :: downshift l k).
    { simpl; rewrite Hlt... }
    rewrite H.
    app_nat_fun_unfold (downshift l k) f b a.
    app_nat_fun_unfold l f b a.
    rewrite<- H.
    simpl in Hal, Had.
    apply andb_prop in Hal as (Hlt' & Hal)...
    apply andb_prop in Had as (nHin' & Had)...
    rewrite IHf...
    rewrite H.
    clear - Hlt nHin Hal Had Hlt' nHin'.
    destruct a.
    + change (nth (b :: downshift l k) b 0) with b.
      change (nth (b :: l) b 0) with b.
      simpl; rewrite Hlt...
    + change (nth (b :: downshift l k) b (S a)) with (nth (downshift l k) b a).
      change (nth (b :: l) b (S a)) with (nth l b a).
      rewrite downshift_nth...
      * apply Lt.lt_S_n.
        apply Nat.ltb_lt...
      * apply orb_false_iff in nHin as (_ & nHin)...
  - rewrite downshift_gt.
    2:{ apply orb_false_iff in nHin as (nHeq & _).
        apply Nat.eqb_neq in nHeq.
        apply Nat.ltb_nlt in Hlt.
        apply Nat.ltb_lt.
        lia. }
    app_nat_fun_unfold (downshift l k) f (pred b) a.
    pattern (pred b :: downshift l k) at 2.
    rewrite <- downshift_gt.
    2:{ apply orb_false_iff in nHin as (nHeq & _).
        apply Nat.eqb_neq in nHeq.
        apply Nat.ltb_nlt in Hlt.
        apply Nat.ltb_lt.
        lia. }
    simpl in Hal, Had.
    apply andb_prop in Hal as (Hlt' & Hal)...
    apply andb_prop in Had as (nHin' & Had)...
    rewrite IHf...
    app_nat_fun_unfold l f b a.
    destruct a.
    + change (nth (pred b :: downshift l k) (pred b) 0) with (pred b).
      change (nth (b :: l) b 0) with b.
      rewrite downshift_gt...    
      apply orb_false_iff in nHin as (nHeq & _).
      apply Nat.eqb_neq in nHeq.
      apply Nat.ltb_nlt in Hlt.
      apply Nat.ltb_lt.
      lia.
    + change (nth ((pred b) :: downshift l k) (pred b) (S a)) with (nth (downshift l k) (pred b) a).
      change (nth (b :: l) b (S a)) with (nth l b a).
      apply Nat.ltb_lt in Hlt'.
      apply Lt.lt_S_n in Hlt'.
      apply orb_false_iff in nHin as (_ & nHin). 
      replace (nth (downshift l k) (Init.Nat.pred b) a) with (nth (downshift l k) b a).
      2:{ apply nth_correct.
          rewrite downshift_length... }
      rewrite downshift_nth...
Qed.          

(** ** Basic manipulation *)

Lemma map_incr_all {A} : forall (f : nat -> A) l k,
    map f (incr_all l k) = map (fun x => f (k + x)) l.
Proof with try reflexivity; try assumption.
  intros f.
  induction l; intros k...
  simpl.
  rewrite IHl...
Qed.

Lemma nth_correct_map_Id {A} : forall a1 a2 a3 (l : list A),
    map (fun x => nth (a1 :: l) a2 x) (Id (S (length l))) = map (fun x => nth (a1 :: l) a3 x) (Id (S (length l))).
Proof with try reflexivity; try assumption.
  intros a1 a2 a3 l; revert a1 a2 a3; induction l; intros a1 a2 a3...
  change (map (fun x : nat => nth (a1 :: a :: l) a2 x) (Id (S (length (a :: l)))))
    with (a1 :: map (fun x : nat => nth (a1 :: a :: l) a2 x) (incr_all (Id (S (length l))) 1)).
  change (map (fun x : nat => nth (a1 :: a :: l) a3 x) (Id (S (length (a :: l)))))
    with (a1 :: map (fun x : nat => nth (a1 :: a :: l) a3 x) (incr_all (Id (S (length l))) 1)).
  rewrite 2 map_incr_all.
  change (map (fun x : nat => nth (a1 :: a :: l) a2 (1 + x)) (Id (S (length l)))) with (map (fun x : nat => nth (a :: l) a2 x) (Id (S (length l)))).
  change (map (fun x : nat => nth (a1 :: a :: l) a3 (1 + x)) (Id (S (length l)))) with (map (fun x : nat => nth (a :: l) a3 x) (Id (S (length l)))).
  rewrite IHl with a a2 a3...
Qed. 

Lemma app_Id {A} : forall (l : list A),
    app_nat_fun l (Id (length l)) = l.
Proof with try reflexivity; try assumption.
  induction l...
  simpl.
  change (fun x0 : nat => match x0 with
                          | 0 => a
                          | S n => nth l a n
                          end) with (fun x0 => nth (a :: l) a x0).
  rewrite map_incr_all.
  change (map (fun x : nat => nth (a :: l) a (1 + x)) (Id (length l))) with (map (fun x : nat => nth l a x) (Id (length l))).
  replace (map (fun x : nat => nth l a x) (Id (length l))) with l...
  symmetry.
  transitivity (app_nat_fun l (Id (length l)))...
  unfold app_nat_fun.
  destruct l...
  apply nth_correct_map_Id. 
Qed.

Lemma asso_compo {A} : forall (l1 : list A) l2 l3,
    app_nat_fun l1 (app_nat_fun l2 l3) = app_nat_fun (app_nat_fun l1 l2) l3.
Proof with try reflexivity; try assumption.
  intros l1 l2 l3.
  destruct l1...
  rename a into n.
  destruct l2...
  unfold app_nat_fun.
  change (match map (fun x0 : nat => nth (n :: l1) n x0) (n0 :: l2) with
          | nil => nil
          | a :: l => map (fun x : nat => nth (a :: l) a x) l3
          end)
    with (map (fun x0 => nth ((nth (n :: l1) n n0) :: map (fun x1 => nth (n :: l1) n x1) l2) (nth (n :: l1) n n0) x0) l3).
  revert n l1 n0 l2; induction l3; intros n l1 n0 l2...
  change (map (fun x0 : nat => nth (n :: l1) n x0)
              (map (fun x1 : nat => nth (n0 :: l2) n0 x1) (a :: l3))) with
      (nth (n :: l1) n (nth (n0 :: l2) n0 a) :: (map (fun x0 : nat => nth (n :: l1) n x0)
                                                     (map (fun x1 : nat => nth (n0 :: l2) n0 x1) l3))).
  change (map
    (fun x0 : nat =>
     nth (nth (n :: l1) n n0 :: map (fun x1 : nat => nth (n :: l1) n x1) l2)
         (nth (n :: l1) n n0) x0) (a :: l3)) with
      (nth (nth (n :: l1) n n0 :: (map (fun x1 => nth (n :: l1) n x1) l2)) (nth (n :: l1) n n0) a :: map
    (fun x0 : nat =>
     nth (nth (n :: l1) n n0 :: map (fun x1 : nat => nth (n :: l1) n x1) l2)
         (nth (n :: l1) n n0) x0) l3).
  replace (nth (nth (n :: l1) n n0 :: map (fun x1 : nat => nth (n :: l1) n x1) l2)
               (nth (n :: l1) n n0) a) with
      ( nth (n :: l1) n (nth (n0 :: l2) n0 a)).
  2:{ case_eq (a <? (length (n0 :: l2))); intros Hlt.
      - clear - Hlt.
        revert a n0 Hlt.
        induction l2; intros b n0 Hlt.
        + destruct b; try destruct b...
        + destruct b...
          change (nth (n0 :: a :: l2) n0 (S b)) with (nth (a :: l2) n0 b).
          change (nth (nth (n :: l1) n n0 :: map (fun x1 : nat => nth (n :: l1) n x1) (a :: l2))
                      (nth (n :: l1) n n0) (S b))
            with (nth (nth (n :: l1) n a :: map (fun x1 => nth (n :: l1) n x1) l2) (nth (n :: l1) n n0) b).
          replace (nth (a :: l2) n0 b) with (nth (a :: l2) a b).
          2:{ apply nth_correct.
              apply Nat.ltb_lt in Hlt.
              simpl in Hlt.
              simpl.
              lia. }
          replace (nth (nth (n :: l1) n a :: map (fun x1 : nat => nth (n :: l1) n x1) l2)
                       (nth (n :: l1) n n0) b)
            with (nth (nth (n :: l1) n a :: map (fun x1 : nat => nth (n :: l1) n x1) l2)
                      (nth (n :: l1) n a) b).
          2:{ apply nth_correct.
              apply Nat.ltb_lt in Hlt.
              simpl in Hlt.
              simpl.
              rewrite map_length.
              lia. }
          apply IHl2...
      - apply Nat.ltb_nlt in Hlt.
        replace (nth (n0 :: l2) n0 a) with n0.
        2:{ symmetry.
            apply nth_ge.
            lia. }
        symmetry.
        apply nth_ge.
        simpl.
        rewrite map_length.
        simpl in Hlt.
        lia. }
  replace (map
       (fun x0 : nat =>
        nth (nth (n :: l1) n n0 :: map (fun x1 : nat => nth (n :: l1) n x1) l2)
            (nth (n :: l1) n n0) x0) l3) with
      (map (fun x : nat => nth (n :: l1) n x)
           (map (fun x : nat => nth (n0 :: l2) n0 x) l3))...
  apply IHl3.
Qed.          

Lemma Id_length : forall n, length (Id n) = n.
Proof with try reflexivity; try assumption.
  induction n...
  simpl; rewrite incr_all_length; rewrite IHn...
Qed.

Lemma app_nat_fun_right {A} : forall (l1 : list A) l2 f,
    all_lt f (length l2) = true ->
    app_nat_fun (l1 ++ l2) (incr_all f (length l1)) = app_nat_fun l2 f.
Proof with try reflexivity; try assumption.
  intros l1 l2 f; revert l1 l2.
  induction f; intros l1 l2 Hal; destruct l1; try now destruct l2.
  - rewrite incr_all_0...
  - change (app_nat_fun ((a0 :: l1) ++ l2) (incr_all (a :: f) (length (a0 :: l1))))
      with
        ((nth ((a0 :: l1) ++ l2) a0 ((length (a0 :: l1)) + a)) :: (app_nat_fun ((a0 :: l1) ++ l2) (incr_all f (length (a0 :: l1))))).
    destruct l2.
    { inversion Hal. }
    change (app_nat_fun (a1 :: l2) (a :: f)) with ((nth (a1 :: l2) a1 a) :: (app_nat_fun (a1 :: l2) f)).
    apply andb_prop in Hal as (Hlt & Hal).
    rewrite (IHf _ _ Hal).
    replace (nth (a1 :: l2) a1 a) with (nth ((a0 :: l1) ++ a1 :: l2) a0 (length (a0 :: l1) + a))...
    rewrite nth_plus.
    apply nth_correct.
    simpl.
    apply Nat.ltb_lt...
Qed.

Lemma app_nat_fun_left {A} : forall (l1 l2 : list A) f,
    all_lt f (length l1) = true ->
    app_nat_fun (l1 ++ l2) f = app_nat_fun l1 f.
Proof with try reflexivity; try assumption.
  intros l1 l2; induction f; intros Hal.
  - destruct l1; destruct l2...
  - destruct l1; try now inversion Hal.
    change (app_nat_fun ((a0 :: l1) ++ l2) (a :: f)) with (nth ((a0 :: l1) ++ l2) a0 a :: app_nat_fun ((a0 :: l1) ++ l2) f).
    rewrite IHf.
    2:{ apply andb_prop in Hal as (_ & Hal)... }
    app_nat_fun_unfold l1 f a0 a.
    replace (nth (a0 :: l1) a0 a) with (nth ((a0 :: l1) ++ l2) a0 a)...
    rewrite nth_left...
    apply andb_prop in Hal as (Hlt & _).
    apply Nat.ltb_lt in Hlt...
Qed.

Definition cfun n m := incr_all (Id m) n ++ (Id n).

Lemma cfun_length : forall n m, length (cfun n m) = n + m.
Proof with try reflexivity.
  intros.
  unfold cfun.
  rewrite app_length; rewrite incr_all_length; rewrite 2 Id_length.
  apply Nat.add_comm.
Qed.

Lemma all_lt_cfun : forall n m, all_lt (cfun n m) (n + m) = true.
Proof with try assumption; try reflexivity.
  intros n m.
  unfold cfun.
  rewrite all_lt_app.
  splitb.
  - rewrite <- all_lt_incr_all.
    apply all_lt_Id.
  - apply all_lt_leq with n; [apply all_lt_Id | lia].
Qed.

Lemma all_distinct_cfun : forall n m, all_distinct (cfun n m) = true.
Proof with try assumption; try reflexivity.
  intros n m.
  unfold cfun.
  rewrite all_distinct_app_commu.
  apply all_distinct_app; try apply all_lt_Id; try apply all_distinct_Id.
Qed.
  
Lemma app_cfun_eq {A} : forall (l1 : list A) l2,
    l2 ++ l1 = app_nat_fun (l1 ++ l2) (cfun (length l1) (length l2)).
Proof with try reflexivity; try assumption.
  intros l1 l2; revert l1.
  induction l2; intros l1.
  - simpl.
    change (cfun (length l1) 0) with (Id (length l1)).
    rewrite app_nil_r.
    rewrite app_Id...
  - simpl.
    unfold cfun.
    change (Id (S (length l2))) with (0 :: (incr_all (Id (length l2)) 1)).
    replace (incr_all (0 :: incr_all (Id (length l2)) 1) (length l1)) with ((length l1) :: incr_all (incr_all (Id (length l2)) (length l1)) 1).
    2:{ simpl.
        rewrite Nat.add_0_r.
        rewrite incr_all_incr_all... }
    simpl.
    rewrite app_nat_fun_middle.
    replace (app_nat_fun (l1 ++ a :: l2)
                         (incr_all (incr_all (Id (length l2)) (length l1)) 1 ++ Id (length l1))) with (l2 ++ l1)...
    rewrite app_nat_fun_downshift.
    + rewrite downshift_app.
      rewrite<- incr_all_plus.
      replace (length l1 + 1) with (S (length l1)) by lia.
      rewrite downshift_incr_all.
      rewrite IHl2.
      replace (downshift (Id (length l1)) (length l1)) with (Id (length l1))...
      rewrite downshift_if_all_lt...
      apply all_lt_Id.
    + rewrite In_nat_bool_app.
      apply orb_false_iff.
      split.
      * rewrite<- incr_all_plus.
        apply negb_In_incr_all.
        lia.
      * apply all_lt_In_nat_bool_false.
        apply all_lt_Id.
    + rewrite all_lt_app.
      apply andb_true_iff.
      split.
      * rewrite<- incr_all_plus.
        replace (length l1 + 1) with (S (length l1)) by lia.
        rewrite app_length.
        change (S (length l1 + length l2)) with ((S (length l1)) + length l2).
        rewrite<- all_lt_incr_all.
        apply all_lt_Id.
      * apply all_lt_leq with (length l1).
        -- apply all_lt_Id.
        -- rewrite app_length.
           lia.
Qed.

(** ** append function *)

Lemma app_nat_fun_all_lt {A} : forall (l1 : list A) l2 f,
    all_lt f (length l1) = true ->
    app_nat_fun (l1 ++ l2) f = app_nat_fun l1 f.
Proof with try reflexivity; try assumption.
  intros l1 l2 f; revert l1 l2.
  induction f; intros l1 l2 Hal; destruct l1; try now destruct l2.
  change (app_nat_fun ((a0 :: l1) ++ l2) (a :: f)) with (nth (a0 :: l1 ++ l2) a0 a :: (app_nat_fun ((a0 :: l1) ++ l2) f)).
  change (app_nat_fun (a0 :: l1) (a :: f)) with (nth (a0 :: l1) a0 a :: app_nat_fun (a0 :: l1) f).
  simpl in Hal.
  change (S (length l1)) with (length (a0 :: l1)) in Hal.
  apply andb_prop in Hal as (Hlt & Hal).
  rewrite IHf...
  replace (nth (a0 :: l1) a0 a) with (nth (a0 :: l1 ++ l2) a0 a)...
  apply (nth_left (a0 :: l1)).
  apply Nat.ltb_lt...
Qed.

Lemma app_nat_fun_app {A} : forall (l : list A) f1 f2,
    app_nat_fun l (f1 ++ f2) = app_nat_fun l f1 ++ app_nat_fun l f2.
Proof with try reflexivity; try assumption.
  intros l f1; revert l.
  induction f1; intros l f2; destruct l...
  change (app_nat_fun (a0 :: l) ((a :: f1) ++ f2)) with
      (nth (a0 :: l) a0 a :: app_nat_fun (a0 :: l) (f1 ++ f2)).
  change (app_nat_fun (a0 :: l) (a :: f1)) with
      (nth (a0 :: l) a0 a :: app_nat_fun (a0 :: l) f1).
  rewrite IHf1...
Qed.  

Lemma append_fun_eq {A} : forall (l1 : list A) l2 f1 f2,
    all_lt f1 (length l1) = true ->
    all_lt f2 (length l2) = true ->
    app_nat_fun (l1 ++ l2) (f1 ++ (incr_all f2 (length l1))) = (app_nat_fun l1 f1) ++ (app_nat_fun l2 f2).
Proof with try reflexivity; try assumption.
  intros l1 l2 f1; revert l1 l2.
  induction f1; intros l1 l2 f2 Hal1 Hal2; destruct l1.
  - simpl.
    rewrite incr_all_0...
  - rewrite 2 app_nil_l.
    apply app_nat_fun_right...
  - inversion Hal1.
  - rewrite app_nat_fun_app.
    rewrite app_nat_fun_right...
    rewrite app_nat_fun_all_lt...
Qed.

Lemma append_fun_all_lt : forall l1 l2 n1 n2,
    all_lt l1 n1 = true ->
    all_lt l2 n2 = true ->
    all_lt (l1 ++ (incr_all l2 n1)) (n1 + n2) = true.
Proof with try reflexivity; try assumption.
  intros l1 l2 n1 n2 Hal1 Hal2.
  rewrite all_lt_app.
  apply andb_true_iff.
  split.
  - apply all_lt_leq with n1...
    lia...
  - rewrite<- all_lt_incr_all...
Qed.

Lemma app_nat_fun_downshift_shift : forall l f n0 n,
    all_distinct l = true ->
    all_distinct f = true ->
    all_lt f (pred (length l)) = true ->
    n < length l ->
    app_nat_fun (downshift l (nth l n0 n)) f = downshift (app_nat_fun l (shift f n)) (nth l n0 n).
Proof with try reflexivity; try assumption.
  intros l f n0 n Had Hadf Hal Hlen.
  destruct (nth_decomp l n0 n) as ((la & lb) & (Hlenla & Heql))...
  pattern l at 1 3.
  rewrite Heql.
  pattern n at 4.
  rewrite<- Hlenla.
  rewrite Heql in Hal.
  destruct la.
  - destruct lb.
    { destruct n; try now inversion Hlenla.
      clear.
      rewrite app_nil_l.
      rewrite downshift_eq.
      induction f...
      change (length nil) with 0.
      change (shift (a :: f) 0) with (S a :: (shift f 0)).
      app_nat_fun_unfold (@nil nat) (shift f 0) (nth l n0 0) (S a).
      replace (nth (nth l n0 0 :: nil) (nth l n0 0) (S a)) with (nth l n0 0).
      2:{ destruct a... }
      rewrite downshift_eq... }
    rewrite app_nat_fun_shift...
    2:{ intros H; inversion H. }
    rewrite 2 app_nil_l.
    rewrite downshift_eq.
    apply app_nat_fun_downshift_commu...
    apply all_distinct_right with (@nil nat).
    rewrite <- Heql...
  - simpl in Hal.
    rewrite app_nat_fun_shift.
    + rewrite downshift_app.
      rewrite downshift_eq.
      rewrite<- downshift_app.
      change ((n1 :: la) ++ lb) with (n1 :: la ++ lb).
      rewrite app_nat_fun_downshift_commu...
      * change (n1 :: la ++ lb) with ((n1 :: la) ++ lb).
        rewrite In_nat_bool_app.
        apply orb_false_iff.
        split.
        -- apply all_distinct_left with lb.
           rewrite<- Heql...
        -- apply all_distinct_right with (n1 :: la).
           rewrite<- Heql...
      * simpl.
        rewrite app_length in Hal |- *.
        simpl in Hal.
        rewrite Nat.add_succ_r in Hal...
    + intros H; inversion H.
    + simpl.
      rewrite app_length in Hal |- * .
      simpl in Hal.
      rewrite Nat.add_succ_r in Hal...
Qed.

Lemma nth_incr_all : forall l n n0 k,
    nth (incr_all l n) (n + n0) k = n + (nth l n0 k).
Proof with try reflexivity.
  induction l; destruct k...
  simpl.
  apply IHl.
Qed.  

Lemma app_nat_fun_incr_all : forall n l p,
    app_nat_fun (incr_all l n) p = incr_all (app_nat_fun l p) n.
Proof with try reflexivity.
  intros n l p.
  destruct l...
  induction p...
  change (incr_all (n0 :: l) n) with (n + n0 :: incr_all l n).
  app_nat_fun_unfold (incr_all l n) p (n + n0) a.
  app_nat_fun_unfold l p n0 a.
  change (n + n0 :: incr_all l n) with (incr_all (n0 :: l) n).
  rewrite IHp.
  change (incr_all (nth (n0 :: l) n0 a :: app_nat_fun (n0 :: l) p) n) with (n + nth (n0 :: l) n0 a :: incr_all (app_nat_fun (n0 :: l) p) n).
  replace (n + nth (n0 :: l) n0 a) with (nth (incr_all (n0 :: l) n) (n + n0) a)...
  apply nth_incr_all.
Qed.

Lemma cfun_inv : forall n m, compo (cfun n m) (cfun m n) = Id (n + m).
Proof with try reflexivity.
  intros n m; unfold compo; unfold cfun.
  rewrite app_nat_fun_app.
  pattern m at 2.
  replace m with (length (incr_all (Id m) n)).
  2:{ rewrite incr_all_length; rewrite Id_length... }
  rewrite app_nat_fun_right.
  2:{ rewrite Id_length; apply all_lt_Id. }
  pattern n at 2.
  replace n with (length (Id n)) by apply Id_length.
  rewrite app_Id.
  rewrite app_nat_fun_left.
  2:{ rewrite incr_all_length; rewrite Id_length; apply all_lt_Id. }
  rewrite app_nat_fun_incr_all.
  pattern m at 2.
  replace m with (length (Id m)) by apply Id_length.
  rewrite app_Id.
  apply Id_incr_all_Id.
Qed.

Lemma incr_all_inj : forall l1 l2 n,
    incr_all l1 n = incr_all l2 n ->
    l1 = l2.
Proof with try reflexivity.
  induction l1; intros l2 n Heq.
  - destruct l2; try now inversion Heq...
  - destruct l2; try now inversion Heq.
    simpl in Heq.
    inversion Heq.
    apply Plus.plus_reg_l in H0.
    apply IHl1 in H1.
    subst...
Qed.    

Lemma cfun_arg_inj : forall n1 n2 m1 m2,
    cfun (S n1) (S m1) = cfun (S n2) (S m2) ->
    n1 = n2 /\ m1 = m2.
Proof with try reflexivity.
  induction n1; intros n2 m1 m2 Heq.
  - unfold cfun in Heq.
    destruct n2, m1, m2; simpl in Heq; try now inversion Heq.
    split...
    inversion Heq.
    apply app_inv_tail in H0.
    clear Heq; rename H0 into Heq.
    revert m2 Heq; induction m1; intros m2 Heq; destruct m2; try now inversion Heq.
    rewrite IHm1 with m2...
    simpl in Heq.
    inversion Heq.
    clear Heq; rename H0 into Heq.
    apply incr_all_inj in Heq.
    apply Heq.
  - destruct n2.
    + unfold cfun in Heq.
      simpl in Heq.
      inversion Heq.
    + unfold cfun in Heq.
      assert (n1 = n2) as Heqn.
      { inversion Heq.
        rewrite<- 2 plus_n_O in H0.
        apply H0. }
      subst.
      apply app_inv_tail in Heq.
      apply incr_all_inj in Heq.
      split...
      apply Nat.succ_inj.
      transitivity (length (Id (S m1))).
      { rewrite Id_length... }
      transitivity (length (Id (S m2))).
      { rewrite Heq... }
      apply Id_length.
Qed.




    


    