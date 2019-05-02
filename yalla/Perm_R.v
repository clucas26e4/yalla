(* ll library for yalla *)

Require Import CMorphisms.
Require Import Lia.
Require Import PeanoNat.
Require Import EqNat.

Require Import Bool_more.
Require Import List_Type_more.
Require Import List_manip.
Require Import List_nat.
Require Import Perm.
Require Import Permutation_Type.
Set Implicit Arguments.

Section Perm_R.
  
  Variable A : Type.
  
  Definition Perm_R (l1 : list A) l2 : Type := {p : Perm & prod (length (projT1 p) = length l1) (l2 = app_perm l1 p)}.
  
End Perm_R.
(* Some facts about Perm_R *)

Lemma Perm_R_nil {A} : forall (l : list A),
    Perm_R nil l -> l = nil.
Proof with try reflexivity; try assumption.
  intros l Hperm.
  destruct Hperm as ((f & Hp) & (Hlen & Heq)).
  rewrite Heq...
Qed.

Lemma Perm_R_nil_cons {A} : forall (l : list A) x,
    Perm_R nil (x :: l) -> False.
Proof with try reflexivity; try assumption.
  intros l x Hperm.
  destruct Hperm as ((f & Hp) & (Hlen & Heq)).
  inversion Heq.
Qed.

Lemma Perm_R_skip {A} : forall l l' (x : A),
    Perm_R l l' ->
    Perm_R (x :: l) (x :: l').
Proof with try reflexivity; try assumption.
  intros l l' x ((p & Hperm) & (Hlen & Heq)).
  split with (next_perm (existT _ p Hperm)).
  split.
  - simpl.
    rewrite incr_all_length.
    rewrite <- Hlen...
  - rewrite Heq.
    unfold app_perm.
    simpl.
    change (map (fun x0 : nat => match x0 with
                          | 0 => x
                          | S n => nth l x n
                                 end) (incr_all p 1)) with (app_nat_fun ((x :: nil) ++ l) (incr_all p (length (x :: nil)))).
    rewrite app_nat_fun_right...
    simpl in Hlen.
    clear Heq.
    apply andb_prop in Hperm as (Hal & _).
    rewrite <- Hlen...
Defined.

Lemma Perm_R_swap {A} : forall l (x y : A),
    Perm_R (x :: y :: l) (y :: x :: l).
Proof with try reflexivity; try assumption.
  intros l x y.
  split with (transpo_perm (length l)).
  split.
  - simpl.
    rewrite incr_all_length.
    rewrite Id_length...
  - simpl.
    change (map
              (fun x0 : nat =>
                 match x0 with
                 | 0 => x
                 | 1 => y
                 | S (S n0) => nth l x n0
                 end) (incr_all (Id (length l)) 2)) with
        (app_nat_fun ((x :: y :: nil) ++ l) (incr_all (Id (length l)) (length (x :: y :: nil)))).
    rewrite app_nat_fun_right.
    + rewrite app_Id...
    + apply all_lt_Id.
Defined.

(* Permutation over lists is an equivalence relation *)

Lemma Perm_R_refl {A} : forall (l : list A),
    Perm_R l l.
Proof with try reflexivity.
  intro l.
  split with (Id_perm (length l)).
  split.
  - unfold Id_perm.
    simpl; rewrite Id_length...
  - unfold app_perm.
    unfold Id_perm.
    simpl.
    rewrite app_Id...
Defined.

Lemma Perm_R_trans {A} : forall (l1 l2 l3 : list A),
    Perm_R l1 l2 ->
    Perm_R l2 l3 ->
    Perm_R l1 l3.
Proof with try reflexivity; try assumption.
  intros l1 l2 l3 IHHp1 IHHp2.
  destruct IHHp1 as (p1 & (Hlen1 & IHHp1)).
  destruct IHHp2 as (p2 & (Hlen2 & IHHp2)).
  assert (length (projT1 p1) = length (projT1 p2)).
  { transitivity (length l2); [ | now symmetry].
    rewrite Hlen1.
    rewrite IHHp1.
    symmetry; apply app_perm_length... }
  split with (compo_perm p1 p2 H).
  split.
  + destruct p1 as (p1 & Hperm1).
    destruct p2 as (p2 & Hperm2).
    unfold compo_perm; simpl.
    unfold compo.
    destruct p1.
    * destruct l1...
    * unfold app_nat_fun.
      rewrite map_length.
      simpl in Hlen2.
      rewrite Hlen2.
      rewrite IHHp1.
      apply app_perm_length...
  + rewrite distri_perm.
    rewrite<- IHHp1...
Defined.

Lemma Perm_R_sym {A} : forall (l1 l2 : list A),
    Perm_R l1 l2 ->
    Perm_R l2 l1.
Proof with try reflexivity; try assumption.
  intros l1 l2 ((p & Hperm) & (Hlen & Heq)).
  unfold app_perm in Heq.
  simpl in *.
  destruct (perm_has_inv p Hperm) as (p_inv & (Heq_inv & (Hperm_inv & Hlen_eq))).
  split with (existT _ p_inv Hperm_inv).
  simpl; split.
  - rewrite Heq.
    change (app_nat_fun l1 p) with (app_perm l1 (existT _ p Hperm)).
    rewrite app_perm_length...
    rewrite<- Hlen_eq...
  - unfold app_perm; simpl.
    rewrite<- (app_Id l1).
    rewrite <- Hlen.
    rewrite<- Heq_inv.
    rewrite Heq.
    rewrite asso_compo...
Defined.

Instance Perm_R_Equivalence A : Equivalence (@Perm_R A) | 10 := {
  Equivalence_Reflexive := @Perm_R_refl A ;
  Equivalence_Symmetric := @Perm_R_sym A ;
  Equivalence_Transitive := @Perm_R_trans A }.

Instance Perm_R_cons A :
 Proper (Logic.eq ==> @Perm_R A ==> @Perm_R A) (@cons A) | 10.
Proof with try reflexivity; try assumption.
  unfold Proper.
  repeat intro.
  destruct X as ((p & Hperm) & (Hlen & Heq)).
  rewrite H.
  split with (next_perm (existT _ p Hperm)).
  simpl; split.
  - rewrite incr_all_length.
    simpl in Hlen; rewrite Hlen...
  - unfold app_perm in Heq.
    simpl in Heq.
    rewrite Heq.
    change (map (fun x1 => match x1 with
                   | 0 => y
                   | S n => nth x0 y n
                      end) (incr_all p 1)) with (app_nat_fun ((y :: nil) ++ x0) (incr_all p (length (y :: nil)))).
    rewrite app_nat_fun_right...
    simpl in Hlen.
    rewrite<- Hlen.
    apply andb_prop in Hperm as (Hal & _)...
Defined.

Hint Resolve Perm_R_refl Perm_R_skip.

(* These hints do not reduce the size of the problem to solve and they
   must be used with care to avoid combinatoric explosions *)
Local Hint Resolve Perm_R_swap Perm_R_trans.
Local Hint Resolve Perm_R_sym.

Section Perm_R_properties.

Context {A : Type}.

Implicit Types a b : A.
Implicit Types l m : list A.

(* Compatibility with others operations on lists *)

Lemma Perm_R_length : forall (l1 l2 : list A),
    Perm_R l1 l2 ->
    length l1 = length l2.
Proof with try reflexivity.
  intros l1 l2 ((f & Hp) & (Hlen & Heq)).
  simpl in Hlen.
  rewrite Heq.
  symmetry.
  apply app_perm_length.
  apply Hlen.
Qed.

Lemma Perm_R_app_tail : forall (l l' tl : list A),
 Perm_R l l' -> Perm_R (l++tl) (l'++tl).
Proof with try reflexivity; try assumption.
  intros l l' tl (p & (Hlen & Heq)).
  split with (append_perm p (Id_perm (length tl))).
  destruct p as (p & Hperm).
  split.
  - unfold append_perm.
    simpl.
    rewrite ? app_length.
    rewrite incr_all_length.
    rewrite Id_length.
    rewrite <- Hlen...
  - unfold append_perm; unfold app_perm.
    simpl.
    simpl in Hlen.
    rewrite Hlen.
    rewrite append_fun_eq.
    + rewrite app_Id.
      rewrite Heq...
    + clear Heq.
      apply andb_prop in Hperm as (Hal & _).
      rewrite<- Hlen...
    + apply all_lt_Id.
Defined.

Lemma Perm_R_app_head : forall (l tl tl' : list A),
 Perm_R tl tl' -> Perm_R (l++tl) (l++tl').
Proof with try assumption; try reflexivity.
  intros l tl tl' (p & (Hlen & Heq)).
  split with (append_perm (Id_perm (length l)) p).
  destruct p as (p & Hperm).
  split.
  - unfold append_perm.
    simpl.
    rewrite ? app_length.
    rewrite incr_all_length.
    rewrite Id_length.
    rewrite <- Hlen...
  - unfold append_perm; unfold app_perm.
    simpl.
    simpl in Hlen.
    rewrite Id_length.
    rewrite append_fun_eq.
    + rewrite app_Id.
      rewrite Heq...
    + apply all_lt_Id.
    + clear Heq.
      apply andb_prop in Hperm as (Hal & _).
      rewrite<- Hlen...
Defined.

Theorem Perm_R_app : forall (l m l' m' : list A),
 Perm_R l l' -> Perm_R m m' -> Perm_R (l++m) (l'++m').
Proof with try assumption; try reflexivity.
  intros l m l' m' (pl & (Hlenl & Heql)) (pm & (Hlenm & Heqm)).
  split with (append_perm pl pm).
  destruct pl as (pl & Hperml).
  destruct pm as (pm & Hpermm).
  unfold append_perm in *; unfold app_perm in *; simpl in *.
  split.
  - rewrite 2 app_length.
    rewrite incr_all_length.
    rewrite Hlenl; rewrite Hlenm...
  - rewrite Hlenl.
    rewrite append_fun_eq.
    + rewrite Heql; rewrite Heqm...
    + apply andb_prop in Hperml as (Hal & _).
      rewrite <- Hlenl...
    + apply andb_prop in Hpermm as (Hal & _).
      rewrite <- Hlenm...
Defined.

Global Instance Perm_R_app' :
 Proper (@Perm_R A ==> @Perm_R A ==> @Perm_R A) (@app A) | 10.
Proof.
  repeat intro; now apply Perm_R_app.
Defined.

Lemma Perm_R_add_inside : forall a (l l' tl tl' : list A),
  Perm_R l l' -> Perm_R tl tl' ->
  Perm_R (l ++ a :: tl) (l' ++ a :: tl').
Proof with try reflexivity; try assumption.
  intros a l l' tl tl' (pl & (Hlenl & Heql)) (ptl & (Hlentl & Heqtl)).
  split with (append_perm pl (next_perm ptl)).
  destruct pl as (pl & Hperml); destruct ptl as (ptl & Hpermtl).
  unfold append_perm in *; unfold app_perm in *; simpl in *.
  split.
  - rewrite 2 app_length.
    simpl.
    rewrite 2 incr_all_length.
    rewrite Hlenl; rewrite Hlentl...
  - rewrite Hlenl.
    change (length l + 0 :: incr_all (incr_all ptl 1) (length l)) with (incr_all (0 :: (incr_all ptl 1)) (length l)).
    rewrite append_fun_eq.
    + app_nat_fun_unfold tl (incr_all ptl 1) a 0.
      change (a :: tl) with ((a :: nil) ++ tl).
      change 1 with (length (a :: nil)).
      rewrite app_nat_fun_right.
      2:{ rewrite<- Hlentl.
          apply andb_prop in Hpermtl as (Hal & _)... }
      rewrite Heql; rewrite Heqtl...
    + rewrite<- Hlenl.
      apply andb_prop in Hperml as (Hal & _)...
    + simpl.
      rewrite <- all_lt_incr_all.
      rewrite<- Hlentl.
      apply andb_prop in Hpermtl as (Hal & _)...
Defined.  

Lemma Perm_R_cons_append : forall (l : list A) x,
  Perm_R (x :: l) (l ++ x :: nil).
Proof with try reflexivity; try assumption.
  intros l x.
  split with (cperm 1 (length l)).
  split.
  - unfold cperm; unfold cfun; simpl.
    rewrite app_length.
    rewrite incr_all_length.
    rewrite Id_length.
    rewrite Nat.add_comm...
  - change (x :: l) with ((x :: nil) ++ l).
    change 1 with (length (x :: nil)).
    rewrite app_cperm_eq...
Defined.  
Local Hint Resolve Perm_R_cons_append.

Theorem Perm_R_app_comm : forall (l l' : list A),
  Perm_R (l ++ l') (l' ++ l).
Proof with try reflexivity; try assumption.
  intros l l'.
  split with (cperm (length l) (length l')).
  split.
  - unfold cperm; unfold cfun; simpl.
    rewrite 2 app_length.
    rewrite incr_all_length.
    rewrite 2 Id_length.
    rewrite Nat.add_comm...
  - rewrite app_cperm_eq...
Qed.    
Local Hint Resolve Perm_R_app_comm.

Theorem Perm_R_cons_app : forall (l l1 l2:list A) a,
  Perm_R l (l1 ++ l2) -> Perm_R (a :: l) (l1 ++ a :: l2).
Proof with auto.
  intros l l1 l2 a Hperm.
  transitivity (a :: (l1 ++ l2))...
  transitivity (a :: (l2 ++ l1))...
  change (a :: l2 ++ l1) with ((a :: l2) ++ l1)...
Defined.
Local Hint Resolve Perm_R_cons_app.

Lemma Perm_R_Add_Type a l l' : Add_Type a l l' -> Perm_R (a::l) l'.
Proof.
  induction 1; simpl; trivial.
  eapply Perm_R_trans ; [ apply Perm_R_swap | ].
  now apply Perm_R_skip.
Defined.

Theorem Perm_R_middle : forall (l1 l2:list A) a,
    Perm_R (a :: l1 ++ l2) (l1 ++ a :: l2).
Proof.
  auto.
Defined.
Local Hint Resolve Perm_R_middle.

Theorem Perm_R_rev : forall (l : list A), Perm_R l (rev l).
Proof.
  induction l as [| x l]; simpl; trivial.
  eapply Perm_R_trans ; [ apply Perm_R_cons_append | ].
  apply Perm_R_app_tail. assumption.
Defined.

Global Instance Perm_R_rev' :
 Proper (@Perm_R A ==> @Perm_R A) (@rev A) | 10.
Proof.
  intros l1 l2 HP.
  eapply Perm_R_trans ; [ | eapply Perm_R_trans ].
  - apply Perm_R_sym.
    apply Perm_R_rev.
  - eassumption.
  - apply Perm_R_rev.
Defined.

Global Instance Perm_R_length' :
  Proper (@Perm_R A ==> Logic.eq) (@length A) | 10.
Proof.
  exact Perm_R_length.
Qed.

Theorem Perm_R_nil_app_cons : forall (l l' : list A) (x : A),
    Perm_R nil (l++x::l') -> False.
Proof.
  intros l l' x Hperm.
  refine (O_S (length l + length l') _).
  apply Perm_R_length in Hperm.
  rewrite app_length in Hperm.
  simpl in Hperm.
  rewrite<- Nat.add_succ_r.
  apply Hperm.
Qed.

Ltac InvAdd_Type := repeat (match goal with
 | H: Add_Type ?x _ (_ :: _) |- _ => inversion H; clear H; subst
 end).

Ltac finish_basic_perms_Type H :=
  try constructor; try rewrite Perm_R_swap; try constructor; trivial;
  (rewrite <- H; now apply Perm_R_Add_Type) ||
  (rewrite H; symmetry; now apply Perm_R_Add_Type).

Theorem Perm_R_cons_inv l l' a :
  Perm_R (a::l) (a::l') -> Perm_R l l'.
Proof with auto.
  intros ((p & Hperm) & (Hlen & Heq)).
  destruct p; try now inversion Heq.
  simpl in Hlen.
  unfold app_perm in Heq.
  change (projT1 (existT (fun l : list nat => is_perm l = true) (n :: p) Hperm)) with (n :: p) in Heq.
  app_nat_fun_unfold l p a n.
  destruct (nth_decomp (a :: l) a n) as ((la & lb) & (Hlenla & Heq')).
  { apply andb_prop in Hperm as (Hal & _).
    apply andb_prop in Hal as (Hlt & _).
    apply Nat.ltb_lt in Hlt.
    simpl in Hlt; rewrite Hlen in Hlt.
    simpl... }
  replace (nth (a :: l) a n) with a in *.
  2:{ inversion Heq.
      rewrite<- H0.
      pattern a at 1.
      rewrite H0... }
  destruct la.
  - split with (existT (fun (l0 : list nat) => is_perm l0 = true) (downshift p n) (tail_perm p n Hperm)).
    split.
    + simpl.
      apply Nat.succ_inj in Hlen.
      rewrite downshift_length...
      clear Heq.
      apply andb_prop in Hperm as (_ & Had).
      apply negb_true_iff.
      apply andb_prop in Had as (nHin & _)...
    + unfold app_perm; simpl.
      apply andb_prop in Hperm as (Hal & Had).
      simpl in Hal, Had.
      apply andb_prop in Hal as (Hlt & Hal).
      apply andb_prop in Had as (nHin & Had).
      inversion Heq'.
      destruct n; try now inversion Hlenla.
      replace (app_nat_fun lb (downshift p 0)) with (app_nat_fun (a :: lb) (incr_all (downshift p 0) 1)).
      2:{ change (a :: lb) with ((a :: nil) ++ lb).
          change 1 with (length (a :: nil)).
          rewrite app_nat_fun_right...
          rewrite<- downshift_all_lt...
          rewrite<- H0.
          rewrite<- Hlen... }
      rewrite incr_all_downshift_0.
      2:{ apply negb_true_iff... }
      rewrite<- H0.
      inversion Heq...
  - inversion Heq'; subst.
    rename a0 into a.
    transitivity (a :: la ++ lb)...
    split with (existT (fun (l0 : list nat) => is_perm l0 = true) (downshift p (S (length la))) (tail_perm p (S (length la)) Hperm)).
    split.
    + simpl.
      apply Nat.succ_inj in Hlen.
      rewrite app_length in Hlen.
      simpl in Hlen.
      rewrite Nat.add_succ_r in Hlen.
      rewrite downshift_length ; [ rewrite app_length | ]...
      clear Heq.
      apply andb_prop in Hperm as (_ & Had).
      apply negb_true_iff.
      apply andb_prop in Had as (nHin & _)...
    + unfold app_perm.
      change (projT1
                (existT (fun l0 : list nat => is_perm l0 = true)
                        (downshift p (S (length la))) (tail_perm p (S (length la)) Hperm)))
        with
          (downshift p (S (length la))).
      change (a :: la ++ lb) with ((a :: la) ++ lb).
      change (S (length la)) with (length (a :: la)).
      rewrite<- app_nat_fun_downshift with _ _ a _.
      * inversion Heq...
      * apply negb_true_iff.
        apply andb_prop in Hperm as (_ & Had).
        apply andb_prop in Had as (nHin & _)...
      * apply andb_prop in Hperm as (Hal & _).
        simpl in Hal.
        apply andb_prop in Hal as (_ & Hal).
        rewrite Hlen in Hal.
        rewrite app_length in Hal.
        simpl in Hal.
        rewrite Nat.add_succ_r in Hal.
        rewrite app_length...
Defined. 

Theorem Perm_R_Add_Type_inv a l1 l2 :
  Perm_R l1 l2 -> forall l1' l2', Add_Type a l1' l1 -> Add_Type a l2' l2 ->
                                  Perm_R l1' l2'.
Proof with auto.
  intros Hperm l1' l2' Hadd1 Hadd2.
  apply Perm_R_cons_inv with a.
  transitivity l1.
  { apply Perm_R_Add_Type... }
  transitivity l2...
  symmetry.
  apply Perm_R_Add_Type...
Defined.

Theorem Perm_R_app_inv (l1 l2 l3 l4:list A) a :
  Perm_R (l1++a::l2) (l3++a::l4) -> Perm_R (l1++l2) (l3 ++ l4).
Proof with auto.
  intros Hperm.
  apply Perm_R_cons_inv with a.  
  transitivity (l1 ++ a :: l2)...
  transitivity (l3 ++ a :: l4)...
Defined.
  
Theorem Perm_R_cons_app_inv l l1 l2 a :
  Perm_R (a :: l) (l1 ++ a :: l2) -> Perm_R l (l1 ++ l2).
Proof with auto.
  intros Hperm.
  apply Perm_R_cons_inv with a.
  transitivity (l1 ++ a :: l2)...
Defined.
  
Theorem Perm_R_app_inv_l : forall l l1 l2,
    Perm_R (l ++ l1) (l ++ l2) -> Perm_R l1 l2.
Proof with auto.
  induction l; intros l1 l2 Hperm; [ | apply IHl; apply Perm_R_cons_inv with a]...
Defined.
           
Theorem Perm_R_app_inv_r l l1 l2 :
  Perm_R (l1 ++ l) (l2 ++ l) -> Perm_R l1 l2.
Proof with auto.
  induction l; intros Hperm; [ rewrite 2 app_nil_r in Hperm | apply IHl; apply Perm_R_app_inv with a]...
Defined.   

Lemma Perm_R_length_1_inv: forall a l, Perm_R (a :: nil) l -> l = (a :: nil).
Proof with try reflexivity.
  intros a l ((p & Hperm) & (Hlen & Heq)).
  unfold app_perm in Heq; simpl in Hlen, Heq.
  rewrite Heq.
  destruct p; try now inversion Hlen.
  destruct p; try now inversion Hlen.
  destruct n...
  apply andb_prop in Hperm as (Hal & _).
  apply andb_prop in Hal as (Hlt & _).
  inversion Hlt.
Qed.

Lemma Perm_R_length_1: forall a b, Perm_R (a :: nil) (b :: nil) -> a = b.
Proof.
  intros a b Hperm.
  apply Perm_R_length_1_inv in Hperm.
  inversion Hperm.
  reflexivity.
Qed.

Lemma Perm_R_length_2_inv :
  forall a1 a2 l, Perm_R (a1 :: a2 :: nil) l -> { l = (a1 :: a2 :: nil) } + { l = (a2 :: a1 :: nil) }.
Proof with try reflexivity.
  intros a1 a2 l ((p & Hperm) & (Hlen & Heq)).
  unfold app_perm in Heq; simpl in Hlen, Heq.
  do 3 (destruct p; try now inversion Hlen).
  destruct n; [ | destruct n].
  - destruct n0 ; [ | destruct n0].
    + apply andb_prop in Hperm as (_ & Had).
      apply andb_prop in Had as (nHin & _).
      inversion nHin.      
    + left.
      rewrite Heq...
    + apply andb_prop in Hperm as (Hal & _).
      apply andb_prop in Hal as (_ & Hal).
      apply andb_prop in Hal as (Hlt & _).
      inversion Hlt.
  - destruct n0 ; [ | destruct n0].
    + right.
      rewrite Heq...
    + apply andb_prop in Hperm as (_ & Had).
      apply andb_prop in Had as (nHin & _).
      inversion nHin.
    + apply andb_prop in Hperm as (Hal & _).
      apply andb_prop in Hal as (_ & Hal).
      apply andb_prop in Hal as (Hlt & _).
      inversion Hlt.
  - apply andb_prop in Hperm as (Hal & _).
    apply andb_prop in Hal as (Hlt & _).
    inversion Hlt.
Qed.

Lemma Perm_R_length_2 :
  forall a1 a2 b1 b2, Perm_R (a1 :: a2 :: nil) (b1 :: b2 :: nil) ->
                      { a1 = b1 /\ a2 = b2 } + { a1 = b2 /\ a2 = b1 }.
Proof with try reflexivity.
  intros a1 a2 b1 b2 Hperm.
  destruct (Perm_R_length_2_inv Hperm) as [Heq | Heq]; inversion Heq.
  - left; split...
  - right; split...
Qed.

Theorem Perm_R_in : forall (l l' : list A) (x : A),
    Perm_R l l' -> In x l -> In x l'.
Proof with try reflexivity; try assumption.
  intros l l' x ((p & Hperm) & (Hlen & Heq)) Hin.
  apply cond_In.
  apply cond_In_inv in Hin as [(k , a0) (Hlen' & Heq')].
  unfold app_perm in Heq; simpl in Hlen, Heq.
  destruct l; try now inversion Hlen'.
  rewrite Heq.
  change (app_nat_fun (a :: l) p) with (map (fun x => nth (a :: l) a x) p).
  destruct (perm_surj _ 0 k Hperm) as (i & (Hlen'' & Heq'')).
  { rewrite Hlen.
    simpl in Hlen'.
    simpl; lia. }
  exists (i , a).
  split.
  - rewrite map_length...
  - rewrite<- nth_nth with _ _ _ i _...
    replace (nth p i (fst (i , a))) with k.
    2:{ rewrite <- Heq''; simpl.
        apply nth_correct... }
    transitivity (nth (a :: l) a0 k)...
    apply nth_correct...  
Qed.   

Global Instance Perm_R_in' :
  Proper (Logic.eq ==> @Perm_R A ==> iff) (@In A) | 10.
Proof with try reflexivity; try assumption.
  repeat red; intros; subst; eauto using Perm_R_in.
Qed.

Theorem Perm_R_in_Type : forall (l l' : list A) (x : A),
    Perm_R l l' -> In_Type x l -> In_Type x l'.
Proof with try reflexivity; try assumption.
  intros l l' x ((p & Hperm) & (Hlen & Heq)) Hin.
  apply cond_In_Type.
  apply cond_In_Type_inv in Hin as [(k , a0) (Hlen' & Heq')].
  unfold app_perm in Heq; simpl in Hlen, Heq.
  destruct l; try now (exfalso; inversion Hlen').
  rewrite Heq.
  change (app_nat_fun (a :: l) p) with (map (fun x => nth (a :: l) a x) p).
  destruct (perm_surj _ 0 k Hperm) as (i & (Hlen'' & Heq'')).
  { rewrite Hlen.
    simpl in Hlen'.
    simpl; lia. }
  exists (i , a).
  split.
  - rewrite map_length...
  - rewrite<- nth_nth with _ _ _ i _...
    replace (nth p i i) with k.
    2:{ rewrite <- Heq''; simpl.
        apply nth_correct... }
    transitivity (nth (a :: l) a0 k)...
    apply nth_correct...  
Qed.   

Global Instance Perm_R_in_Type' :
 Proper (Logic.eq ==> @Perm_R A ==> Basics.arrow) (@In_Type A) | 10.
Proof with try reflexivity; try assumption.
  intros l1 l2 Heq l1' l2' HP Hi ; subst.
  eauto using Perm_R_in_Type.
Qed.

End Perm_R_properties.

Section Perm_R_map.

Variable A B : Type.
Variable f : A -> B.

Lemma Perm_R_map l l' :
  Perm_R l l' -> Perm_R (map f l) (map f l').
Proof with try reflexivity; try assumption.
  intros (p & (Hlen & Heq)).
  split with p.
  destruct p as (p & Hperm).
  unfold app_perm in *.
  simpl in *.
  split.
  - rewrite map_length...
  - rewrite app_nat_fun_map.
    rewrite Heq...
Qed.

Global Instance Perm_R_map' :
  Proper (@Perm_R A ==> @Perm_R B) (map f) | 10.
Proof.
  exact Perm_R_map.
Qed.

End Perm_R_map.


(* PERMUTATION_TYPE = PERMUTATION *)
Require Import Permutation_Type_solve.

Lemma Permutation_Type_to_Perm {A} : forall l1 (l2 : list A),
    Permutation_Type l1 l2 ->
    {p : Perm & prod (length (projT1 p) = length l1) (l2 = app_perm l1 p)}.
Proof with try reflexivity; try assumption.
  intros l1 l2 Hp.
  induction Hp.
  - split with (Id_perm 0).
    split...
  - apply Perm_R_skip...
  - apply Perm_R_swap...
  - apply Perm_R_trans with l'...
Defined.

Lemma Perm_to_Permutation_Type {A} : forall (l1 : list A) l2 (p : Perm),
    length (projT1 p) = length l1 ->
    l2 = app_perm l1 p ->
    Permutation_Type l1 l2.
Proof with try reflexivity; try assumption.
  intros l1 l2; revert l1.
  induction l2; intros l1 p Hlen Heq.
  - destruct l1...
    destruct p as (p & Hp); destruct p; inversion Hlen; inversion Heq.
  - destruct p as (p & Hperm).
    simpl in Hlen.
    destruct p.
    { destruct l1; inversion Heq. }
    unfold app_perm in Heq.
    change (app_nat_fun l1
                        (projT1
                           (existT (fun l : list nat => is_perm l = true) (n :: p) Hperm)))
      with (app_nat_fun l1 (n :: p)) in Heq.
    specialize (app_nat_fun_vs_cons l2 l1 a n p Hlen Hperm Heq) as ((la & lb) & (Hlen1 & Heq1)).
    assert (app_nat_fun (la ++ a :: lb) ((length la) :: p) = a :: app_nat_fun (la ++ a :: lb) p).
    { clear.
      destruct la.
      - simpl...
      - simpl.
        replace (nth (la ++ a :: lb) a0 (length la)) with a...
        symmetry.
        apply nth_middle. }
    destruct (andb_prop _ _ Hperm) as (Halt & Had).
    simpl in Had.
    apply andb_prop in Had as (nHin & Had).
    apply negb_true_iff in nHin.
    rewrite<- Hlen1 in nHin.
    destruct (andb_prop _ _ Halt) as (_ & Haltp).
    replace (length (n :: p)) with (S (length (la ++ lb))) in Haltp.
    2:{ rewrite Hlen.
        rewrite Heq1.
        rewrite 2 app_length.
        rewrite<- Nat.add_succ_r... }
    specialize (app_nat_fun_downshift la lb a p nHin Haltp) as H0.
    clear Haltp.
    rewrite Heq1.
    transitivity (a :: la ++ lb); try perm_Type_solve.
    apply Permutation_Type_skip.
    rewrite Hlen1 in H0, H.
    rewrite Heq1 in Heq.
    rewrite H in Heq.
    inversion Heq.
    rewrite<- H2.
    rewrite H0 in H2.
    assert (is_perm (downshift p n) = true).
    { apply tail_perm... }
    remember (existT (fun x => is_perm x = true) (downshift p n) H1) as dp.
    replace (downshift p n) with (projT1 dp) in H2.
    2:{ rewrite Heqdp... }
    change (app_nat_fun (la ++ lb) (projT1 dp)) with (app_perm (la ++ lb) dp) in H2.
    refine (IHl2 (la ++ lb) dp _ H2).
    rewrite Heqdp; simpl.
    rewrite downshift_length.
    + apply Nat.succ_inj.
      simpl in Hlen; rewrite Hlen.
      rewrite Heq1.
      rewrite 2 app_length.
      rewrite<- Nat.add_succ_r...
    + rewrite<- Hlen1...
Qed.

Ltac find_perm l1 l2 H :=
  assert (Perm_R l1 l2) as H;
  [ apply (Permutation_Type_to_Perm l1 l2); perm_Type_solve | ].

Lemma Perm_R_to_Permutation_Type {A} : forall (l1 : list A) l2,
    Perm_R l1 l2 ->
    Permutation_Type l1 l2.
Proof with try assumption; try reflexivity.
  intros l1 l2 HP.
  destruct HP as (p & (Hlen & Heq)).
  apply Perm_to_Permutation_Type with p...
Qed.

Definition Permutation_Type_to_Perm_R {A} : forall l1 (l2 : list A),
    Permutation_Type l1 l2 ->
    Perm_R l1 l2 := Permutation_Type_to_Perm.


Theorem Perm_R_ind_transpo {A} :
 forall P : list A -> list A -> Prop,
   P nil nil ->
   (forall x l l', Perm_R l l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l, P (y :: x :: l) (x :: y :: l)) ->
   (forall l l' l'', Perm_R l l' -> P l l' -> Perm_R l' l'' -> P l' l'' -> P l l'') ->
   forall l l', Perm_R l l' -> P l l'.
Proof with try apply Permutation_Type_to_Perm_R; auto.
  intros P Hnil Hskip Hswap Htrans.
  intros l l' Hperm.
  assert (Hperm' := Perm_R_to_Permutation_Type Hperm).
  induction Hperm'...
  - apply Hskip...
    apply IHHperm'...
  - apply Htrans with l'...
    + apply IHHperm'1...
    + apply IHHperm'2...    
Qed.

Ltac ind_transpo P Hperm :=
  let x := fresh "x" in
  let y := fresh "y" in
  let la := fresh "la" in
  let lb := fresh "lb" in
  let lc := fresh "lc" in
  let Hperm1 := fresh "Hperm1" in
  let IHHperm1 := fresh "IHHperm1" in
  let Hperm2 := fresh "Hperm2" in
  let IHHperm2 := fresh "IHHperm2" in
  refine (Perm_R_ind_transpo P  _ _ _ _ Hperm); clear Hperm; [ | intros x la lb Hperm1 IHHperm1 | intros x y la | intros la lb lc Hperm1 IHHperm1 Hperm2 IHHperm2].
  

Theorem Perm_R_rect_transpo {A} :
 forall P : list A -> list A -> Type,
   P nil nil ->
   (forall x l l', Perm_R l l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l, P (y :: x :: l) (x :: y :: l)) ->
   (forall l l' l'', Perm_R l l' -> P l l' -> Perm_R l' l'' -> P l' l'' -> P l l'') ->
   forall l l', Perm_R l l' -> P l l'.
Proof with try apply Permutation_Type_to_Perm_R; auto.
  intros P Hnil Hskip Hswap Htrans.
  intros l l' Hperm.
  assert (Hperm' := Perm_R_to_Permutation_Type Hperm).
  induction Hperm'...
  - apply Hskip...
    apply IHHperm'...
  - apply Htrans with l'...
    + apply IHHperm'1...
    + apply IHHperm'2...    
Qed.

Ltac rect_transpo P Hperm :=
  let x := fresh "x" in
  let y := fresh "y" in
  let la := fresh "la" in
  let lb := fresh "lb" in
  let lc := fresh "lc" in
  let Hperm1 := fresh "Hperm1" in
  let IHHperm1 := fresh "IHHperm1" in
  let Hperm2 := fresh "Hperm2" in
  let IHHperm2 := fresh "IHHperm2" in
  refine (Perm_R_rect_transpo P  _ _ _ _ Hperm); clear Hperm; [ | intros x la lb Hperm1 IHHperm1 | intros x y la | intros la lb lc Hperm1 IHHperm1 Hperm2 IHHperm2].

Theorem Perm_R_ind_transpo_bis {A} :
 forall P : list A -> list A -> Prop,
   P nil nil ->
   (forall x l l', Perm_R l l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l l', Perm_R l l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
   (forall l l' l'', Perm_R l l' -> P l l' -> Perm_R l' l'' -> P l' l'' -> P l l'') ->
   forall l l', Perm_R l l' -> P l l'.
Proof.
  intros P Hnil Hskip Hswap Htrans.
  assert (forall l, P l l).
  { induction l; auto. }
  apply Perm_R_ind_transpo.
  - apply Hnil.
  - apply Hskip.
  - intros x y l.
    apply Hswap; auto.
  - apply Htrans.
Qed.

Ltac ind_transpo_bis P Hperm :=
  let x := fresh "x" in
  let y := fresh "y" in
  let la := fresh "la" in
  let lb := fresh "lb" in
  let lc := fresh "lc" in
  let Hperm1 := fresh "Hperm1" in
  let IHHperm1 := fresh "IHHperm1" in
  let Hperm2 := fresh "Hperm2" in
  let IHHperm2 := fresh "IHHperm2" in
  refine (Perm_R_ind_transpo_bis P  _ _ _ _ Hperm); clear Hperm; [ | intros x la lb Hperm1 IHHperm1 | intros x y la | intros la lb lc Hperm1 IHHperm1 Hperm2 IHHperm2].

Theorem Perm_R_rect_transpo_bis {A} :
 forall P : list A -> list A -> Type,
   P nil nil ->
   (forall x l l', Perm_R l l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l l', Perm_R l l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
   (forall l l' l'', Perm_R l l' -> P l l' -> Perm_R l' l'' -> P l' l'' -> P l l'') ->
   forall l l', Perm_R l l' -> P l l'.
Proof.
  intros P Hnil Hskip Hswap Htrans.
  assert (forall l, P l l).
  { induction l; auto. }
  apply Perm_R_rect_transpo.
  - apply Hnil.
  - apply Hskip.
  - intros x y l.
    apply Hswap; auto.
  - apply Htrans.
Qed.

Ltac rect_transpo_bis P Hperm :=
  let x := fresh "x" in
  let y := fresh "y" in
  let la := fresh "la" in
  let lb := fresh "lb" in
  let lc := fresh "lc" in
  let Hperm1 := fresh "Hperm1" in
  let IHHperm1 := fresh "IHHperm1" in
  let Hperm2 := fresh "Hperm2" in
  let IHHperm2 := fresh "IHHperm2" in
  refine (Perm_R_rect_transpo_bis P _ _ _ _ Hperm); clear Hperm; [ | intros x la lb Hperm1 IHHperm1 | intros x y la | intros la lb lc Hperm1 IHHperm1 Hperm2 IHHperm2].