(* ll library for yalla *)

Require Import CMorphisms.
Require Import Lia.
Require Import PeanoNat.
Require Import EqNat.

Require Import Bool_more.
Require Import List_Type_more.
Require Import List_manip.
Require Import List_nat.

(* PERMUTATION DEFINITION *)

Definition is_perm (l : list nat) :=
  (all_lt l (length l)) && (all_distinct l).

Definition Perm := {l & is_perm l = true}.

Definition app_perm {A} (l : list A) (p : Perm) :=
  app_nat_fun l (projT1 p).

(* Some facts about is_perm *)

Lemma tail_perm : forall l k,
    is_perm (k :: l) = true ->
    is_perm (downshift l k) = true.
Proof with try reflexivity; try assumption.
  intros l k Hperm.
  apply andb_prop in Hperm as (Hal & Had).
  splitb.
  - simpl in Had, Hal.
    apply andb_prop in Had as (nHin & Had).
    apply negb_true_iff in nHin.
    rewrite downshift_length...
    apply andb_prop in Hal as (Hlt' & Hal).
    rewrite<- downshift_all_lt...
  - clear Hal.
    induction l...
    simpl.
    case_eq (a <? k); intros Hlt.
    + simpl.
      splitb.
      * rewrite downshift_In_nat_bool_lt...
        apply andb_prop in Had as (_ & Had).
        apply andb_prop in Had as (nHin & _)...
      * apply IHl.
        simpl in Had |- *.
        apply andb_prop in Had as (nHin & Had).
        apply andb_prop in Had as (_ & Had).
        apply negb_true_iff in nHin.
        apply orb_false_iff in nHin as (_ & nHin).
        apply negb_true_iff in nHin.
        splitb...
    + case_eq (a =? k); intros nHeq.
      { exfalso.
        simpl in Had.
        apply andb_prop in Had as (nnHeq & _).
        apply negb_true_iff in nnHeq.
        apply orb_false_iff in nnHeq as (nnHeq & _).
        rewrite Nat.eqb_sym in nnHeq.
        rewrite nnHeq in nHeq.
        inversion nHeq. }
      destruct a.
      { exfalso.
        apply Nat.ltb_nlt in Hlt.
        apply Nat.eqb_neq in nHeq.
        lia. }
      simpl.
      simpl in Had.
      apply andb_prop in Had as (H & Had).
      apply andb_prop in Had as (nHin & Had).
      splitb.
      * change a with (pred (S a)).
        rewrite downshift_In_nat_bool_gt...
        apply Nat.ltb_nlt in Hlt.
        apply Nat.eqb_neq in nHeq.
        apply Nat.ltb_lt.
        lia.
      * apply IHl.
        splitb...
        apply negb_true_iff in H.
        apply orb_false_iff in H as (_ & H).
        apply negb_true_iff...   
Qed.

Lemma perm_surj : forall p k0 k,
    is_perm p = true ->
    k < length p ->
    {i & prod (i < length p) (nth p k0 i = k)}.
Proof with try reflexivity; try assumption.
  intro p.
  remember (length p).
  revert p Heqn.
  induction n; intros p Heq k0 k Hperm Hlt.
  - exfalso.
    lia.
  - destruct p; try now inversion Heq.
    destruct (andb_prop _ _ Hperm) as (_ & H).
    apply andb_prop in H as (nHin & _).
    apply negb_true_iff in nHin.
    destruct (Compare_dec.lt_eq_lt_dec k n0) as [[H1 | H2] | H3].
    + assert (k < n) as Hlt'.
      { destruct (andb_prop _ _ Hperm) as (H & _).
        apply andb_prop in H as (Hlt' & _).
        apply Nat.ltb_lt in Hlt'.
        lia. }
      apply tail_perm in Hperm.
      simpl in Heq.
      apply Nat.succ_inj in Heq.
      assert (n = length (downshift p n0)) as Heqd.
      { rewrite downshift_length... }
      destruct (IHn _ Heqd k0 _ Hperm Hlt') as (i & (Hlen & H)).
      split with (S i).
      split.
      * simpl; lia.
      * rewrite<- H.
        symmetry.
        simpl.
        rewrite Heq in Hlen.
        apply nth_lt_downshift...
        rewrite H...
    + split with 0.
      simpl.
      symmetry in H2.
      split...
      lia.
    + destruct k; [ exfalso; lia | ].
      apply Lt.lt_S_n in Hlt.
      apply tail_perm in Hperm.
      simpl in Heq; apply Nat.succ_inj in Heq.
      assert (n = length (downshift p n0)) as Heqd.
      { rewrite downshift_length... }
      destruct (IHn _ Heqd k0 _ Hperm Hlt) as (i & (Hlen & H)).
      split with (S i).
      split.
      * simpl; lia.
      * rewrite<- H.
        symmetry.
        simpl.
        rewrite Heq in Hlen.
        rewrite nth_ge_downshift...
        2:{ lia. }
        destruct k.
        -- destruct n0; [ | exfalso; lia].
           assert {m & nth p k0 i = S m}.
           { clear - Hlen nHin.
             revert i Hlen.
             induction p; intros i Hlen.
             -  simpl in Hlen.
                exfalso.
                lia.
             - destruct i.
               + destruct a.
                 * inversion nHin.
                 * split with a...
               + apply orb_false_elim in nHin as (_ & nHin).
                 apply Lt.lt_S_n in Hlen.
                 destruct (IHp nHin i Hlen) as (m & Heq).
                 split with m... }
           destruct H0 as (m & Heqm).
           rewrite Heqm...
        -- rewrite Nat.lt_succ_pred with k _...
           unfold "<".
           rewrite <- H.
           apply le_nth_downshift...
Qed.

Lemma decomp_perm : forall l k,
    k < length l ->
    is_perm l = true ->
    {' (la , lb) : _ & prod (l = la ++ k :: lb) (prod (In_nat_bool k la = false) (In_nat_bool k lb = false))}.
Proof with try reflexivity; try assumption.
  intros l k Hlen Hperm.
  destruct (perm_surj l 0 k Hperm Hlen) as (i & (Hleni & Heq)).
  destruct (nth_decomp l 0 i Hleni) as ((la & lb) & (Heq_len & Heql)).
  split with (la , lb).
  split; [ | split].
  - rewrite<- Heq...
  - apply andb_prop in Hperm as (_ & Had).
    rewrite Heql in Had.
    rewrite Heq in Had.
    apply all_distinct_left with lb...
  - apply andb_prop in Hperm as (_ & Had).
    rewrite Heql in Had.
    rewrite Heq in Had.
    apply all_distinct_right with la...
Qed.      

Lemma downshift_perm_length : forall l k,
    k < length l -> 
    is_perm l = true ->
    length (downshift l k) = pred (length l).
Proof with try reflexivity; try assumption.
  intros l k Hlen Hperm.
  destruct (decomp_perm l k Hlen Hperm) as ((la & lb) & (Heq & (nHinla & nHinlb))).
  rewrite Heq.
  rewrite downshift_app.
  rewrite 2 app_length.
  rewrite downshift_eq.
  simpl.
  rewrite Nat.add_succ_r.
  rewrite 2 downshift_length...
Qed.  

Lemma downshift_perm : forall l k,
    is_perm l = true ->
    is_perm (downshift l k) = true.
Proof with try reflexivity; try assumption.
  intros l k Hperm.
  case_eq (k <? length l); intros Hlt.
  - apply Nat.ltb_lt in Hlt.
    unfold is_perm in *.
    apply andb_prop in Hperm as (Halt & Had).
    replace (all_distinct (downshift l k)) with true.
    2:{ symmetry.
      apply downshift_keep_all_distinct... }
    replace (all_lt (downshift l k) (length (downshift l k))) with true...
    symmetry.
    rewrite downshift_perm_length...
    2:{ splitb... }
    destruct l; try now inversion Hlt.
    change (length (n :: l)) with (S (length l)) in Halt.
    change (pred (length (n :: l))) with (length l).
    rewrite downshift_all_lt with _ _ k in Halt...
    simpl in Hlt.
    apply Nat.leb_le.
    lia.
  - rewrite downshift_if_all_lt...
    apply Nat.ltb_nlt in Hlt.
    apply andb_prop in Hperm as (Hal & _).
    apply all_lt_leq with (length l)...
    lia.
Qed.
                               
Lemma app_perm_keep_all_distinct : forall (l : list nat) (p : Perm),
    length (projT1 p) = length l ->
    all_distinct l = all_distinct (app_perm l p).
Proof with try reflexivity; try assumption.
  destruct l...
  unfold app_perm.
  unfold app_nat_fun.
  intros p Hlen.
  destruct p as (p & H1).
  assert (Hperm := H1).
  unfold is_perm in H1.
  simpl.
  simpl in Hlen.
  change (negb (In_nat_bool n l) && all_distinct l) with (all_distinct (n :: l)).
  apply andb_prop in H1 as (H1 & H2).
  change (map (fun x : nat => match x with
                              | 0 => n
                                | S n0 => nth l n n0
                              end) p) with (map (fun x => nth (n :: l) n x) p).
  case_eq (all_distinct (n :: l)); intros Hal; symmetry.
  - apply cond_all_distinct.
    intros n1 n2 k Hlt1 Hlt2 Heq.
    assert (H := cond_all_distinct_inv (n :: l)).
    specialize (H Hal) as H.
    clear Hal.
    assert (H0 := cond_all_distinct_inv p).
    specialize (H0 H2).
    rewrite map_length in Hlt1 , Hlt2.
    apply H0 with n...
    apply H with n; try (simpl; rewrite<- Hlen)...
    + apply cond_all_lt_inv...
    + apply cond_all_lt_inv...
    + replace (nth (n :: l) n (nth p n n1)) with (nth (map (fun x => (nth (n :: l) n x)) p) k n1).
      2:{ symmetry.
          replace (nth (map (fun x : nat => nth (n :: l) n x) p) k n1) with (nth (map (fun x : nat => nth (n :: l) n x) p) n n1).
          - apply nth_nth...
          - apply nth_correct.
            rewrite map_length... }
      replace (nth (n :: l) n (nth p n n2)) with (nth (map (fun x => (nth (n :: l) n x)) p) k n2).
      2:{ symmetry.
          replace (nth (map (fun x : nat => nth (n :: l) n x) p) k n2) with (nth (map (fun x : nat => nth (n :: l) n x) p) n n2).
          - apply nth_nth...
          - apply nth_correct.
            rewrite map_length... }
      apply Heq.
  - apply cond_all_distinct_false_inv with _ n in Hal as ((k1 & k2) & (Hlt1 & (Hlt2 & (nHeq & Heq)))).
    simpl in Hlt1 , Hlt2.
    rewrite<- Hlen in Hlt1, Hlt2.
    destruct (perm_surj _ n k1 Hperm Hlt1) as (i1 & (Hlti1 & Heqk1)).
    destruct (perm_surj _ n k2 Hperm Hlt2) as (i2 & (Hlti2 & Heqk2)).
    apply cond_all_distinct_false with n i1 i2.
    + rewrite map_length...
    + rewrite map_length...
    + intro H.
      apply nHeq.
      assert (H0 := cond_all_distinct_inv p).
      apply H0 with n...
      rewrite<- Heqk1.
      rewrite<- Heqk2.
      rewrite H...
    + rewrite<- nth_nth with _ _ _ n _...
      rewrite<- nth_nth with _ _ _ n _ ...
      rewrite Heqk1.
      rewrite Heqk2...
Qed.  
                               
Lemma app_perm_keep_all_lt : forall (l : list nat) n (p : Perm),
    length (projT1 p) = length l ->
    all_lt l n = all_lt (app_perm l p) n.
Proof with try reflexivity; try assumption.
  intros l n p Hlen.
  destruct p as (p & Hperm).
  simpl in Hlen.
  case_eq (all_lt l n); intros Heq; symmetry.
  - destruct l...
    apply cond_all_lt.
    intros k0 k Hlt.
    unfold app_perm.
    unfold app_nat_fun.
    simpl.
    simpl in Hlt.
    change (fun x : nat => match x with
                           | 0 => n0
                           | S n1 => nth l n0 n1
                           end) with (fun x => nth (n0 :: l) n0 x) in *.
    rewrite map_length in Hlt.
    replace (nth (map (fun x : nat => nth (n0 :: l) n0 x) p) k0 k) with (nth (map (fun x : nat => nth (n0 :: l) n0 x) p) n0 k).
    2:{ apply nth_correct.
        rewrite map_length... }
    rewrite<- nth_nth with _ _ _ n0 _...
    apply cond_all_lt_inv...
    apply cond_all_lt_inv...
    apply andb_prop in Hperm as (H & _)...
    rewrite<- Hlen...
  - destruct l; try now inversion Heq...
    simpl.
    change (fun x : nat => match x with
                              | 0 => n0
                              | S n1 => nth l n0 n1
                           end) with (fun x => nth (n0 :: l) n0 x).
    destruct (cond_all_lt_false_inv _ _ Heq n0) as (k & (Hlen' & Hge)).
    rewrite<- Hlen in Hlen'.
    destruct (perm_surj _ n0 k Hperm Hlen') as (i & (Hlen'' & Heqi)).
    apply cond_all_lt_false with i n0.
    + rewrite map_length...
    + rewrite<- nth_nth with _ _ _ n0 _...
      rewrite Heqi...
Qed.

Lemma compo_perm_is_perm : forall l1 l2,
    is_perm l1 = true ->
    is_perm l2 = true ->
    length l1 = length l2 ->
    is_perm (compo l1 l2) = true.
Proof with try reflexivity; try assumption.
  intros l1 l2 Hp1 Hp2 Hlen.
  unfold compo.
  change (app_nat_fun l1 l2) with (app_perm l1 (existT _ l2 Hp2)).
  splitb.
  - rewrite<- app_perm_keep_all_lt.
    2:{ symmetry... }
    unfold app_perm.
    simpl.
    apply andb_prop in Hp1 as (Hp1 & _).
    destruct l1...
    unfold app_nat_fun.
    rewrite map_length.
    rewrite<- Hlen...
  - apply andb_prop in Hp1 as (Halt1 & Had1).
    rewrite<- app_perm_keep_all_distinct with _ (existT (fun l : list nat => is_perm l = true) l2 Hp2)...
    symmetry...
Qed.

Definition compo_perm (l1 : Perm) (l2 : Perm) (Hlen : length (projT1 l1) = length (projT1 l2)):=
  existT (fun l => is_perm l = true) (compo (projT1 l1) (projT1 l2)) (compo_perm_is_perm _ _ (projT2 l1) (projT2 l2) Hlen).

Lemma Id_is_perm : forall n, is_perm (Id n) = true.
Proof with try reflexivity; try assumption.
  intros n.
  splitb.
  - induction n...
    simpl.
    rewrite<- all_lt_incr_all.
    rewrite incr_all_length...
  - apply all_distinct_Id.
Qed.    
    
Lemma transpo_is_perm : forall n, is_perm (1 :: 0 :: (incr_all (Id n) 2)) = true.
Proof with try reflexivity; try assumption.
  intros n; induction n...
  unfold is_perm.
  destruct (andb_prop _ _ IHn) as (H1 & H2).
  splitb.
  - simpl.
    rewrite 2 incr_all_length.
    change (S (S (S (length (Id n))))) with (2 + (S (length (Id n)))).
    rewrite<- all_lt_incr_all.
    rewrite<- all_lt_incr_all.
    simpl in H1.
    rewrite incr_all_length in H1.
    change (S (S (length (Id n)))) with (2 + (length (Id n))) in H1.
    rewrite<- all_lt_incr_all in H1...
  - splitb; [ | splitb].
    + apply negb_true_iff.
      apply negb_In_incr_all.
      lia.
    + apply negb_true_iff.
      apply negb_In_incr_all.
      lia.
    + change ((fix all_distinct (l : list nat) : bool :=
     match l with
     | nil => true
     | n0 :: l0 => negb (In_nat_bool n0 l0) && all_distinct l0
     end) (incr_all (Id (S n)) 2)) with (all_distinct (incr_all (Id (S n)) 2)).
      rewrite<- all_distinct_incr_all.
      apply all_distinct_Id.
Qed.

Lemma next_perm_is_perm : forall l,
    is_perm l = true ->
    is_perm (0 :: (incr_all l 1)) = true.
Proof with try reflexivity; try assumption.
  intros l Hperm.
  apply andb_prop in Hperm as (H1 & H2).
  splitb.
  - splitb.
    + apply Nat.ltb_lt.
      simpl; lia.
    + change ((fix all_lt (l0 : list nat) (n : nat) {struct l0} : bool :=
     match l0 with
     | nil => true
     | k :: l1 => (k <? n) && all_lt l1 n
     end) (incr_all l 1) (length (0 :: incr_all l 1))) with (all_lt (incr_all l 1) (length (0 :: incr_all l 1))).
      simpl; rewrite<- all_lt_incr_all; rewrite incr_all_length...
  - splitb.
    + apply negb_true_iff.
      apply negb_In_incr_all.
      lia.
    + change ((fix all_distinct (l0 : list nat) : bool :=
     match l0 with
     | nil => true
     | n :: l1 => negb (In_nat_bool n l1) && all_distinct l1
     end) (incr_all l 1)) with (all_distinct (incr_all l 1)).
      rewrite<- all_distinct_incr_all...
Qed.

Definition Id_perm n :=
  existT (fun l => is_perm l = true) (Id n) (Id_is_perm n).

Definition transpo_perm n :=
  existT (fun l => is_perm l = true) (1 :: 0 :: (incr_all (Id n) 2)) (transpo_is_perm n).

Definition next_perm (p : Perm) :=
  existT (fun l => is_perm l = true) (0 :: (incr_all (projT1 p) 1)) (next_perm_is_perm (projT1 p) (projT2 p)).

Lemma distri_perm {A} : forall (l :list A) (p1 p2 : Perm)
                               (Hlen : length (projT1 p1) = length (projT1 p2)),
    app_perm l (compo_perm p1 p2 Hlen) = app_perm (app_perm l p1) p2.
Proof with try reflexivity; try assumption.
  intros l p1 p2 Hlen.
  destruct p1 as (p1 & Hp1).
  destruct p2 as (p2 & Hp2).
  unfold app_perm.
  simpl.
  unfold compo.
  apply asso_compo.
Qed.

Lemma length_app_perm {A} : forall l (a : A) (p : Perm),
    length (app_perm (a :: l) p) = length (projT1 p).
Proof with try reflexivity; try assumption.
  intros l a p.
  destruct p as (p & Hperm).
  unfold app_perm.
  unfold app_nat_fun.
  rewrite map_length...
Qed.

Lemma perm_ext : forall (p1 : Perm) p2,
    projT1 p1 = projT1 p2 ->
    p1 = p2.
Proof with try reflexivity.
  intros p1 p2 Heq.
  destruct p1 as (p1 & Hperm1).
  destruct p2 as (p2 & Hperm2).
  simpl in Heq.
  subst.
  replace Hperm1 with Hperm2...
  apply UIP_bool.
Qed.

Lemma cfun_is_perm : forall n m,
    is_perm (cfun n m) = true.
Proof with try reflexivity; try assumption.
  intros n m.
  unfold is_perm.
  unfold cfun.
  apply andb_true_iff.
  split.
  - rewrite app_length.
    rewrite incr_all_length.
    rewrite 2 Id_length.
    rewrite all_lt_app.
    splitb.
    * rewrite Nat.add_comm.
      rewrite<- all_lt_incr_all.
      apply all_lt_Id.
    * apply all_lt_leq with n; [apply all_lt_Id | lia].
  - rewrite all_distinct_app_commu.
    rewrite Id_incr_all_Id.
    apply all_distinct_Id.
Qed.

Definition cperm n m :=
  existT (fun l => is_perm l = true) (cfun n m) (cfun_is_perm n m).

Lemma append_perm_is_perm : forall f1 f2,
    is_perm f1 = true ->
    is_perm f2 = true ->
    is_perm (f1 ++ (incr_all f2 (length f1))) = true.
Proof with try reflexivity; try assumption.
  intros f1 f2 Hp1 Hp2.
  apply andb_prop in Hp1 as (Hal1 & Had1).
  apply andb_prop in Hp2 as (Hal2 & Had2).
  splitb.
  - rewrite app_length.
    rewrite incr_all_length.
    apply append_fun_all_lt...
  - remember (length f1) as n.
    clear Heqn Hal2.
    revert n Hal1.
    induction f1; intros n Hal.
    + simpl; rewrite<- all_distinct_incr_all...
    + simpl in Had1, Hal |- *.
      splitb.
      * apply negb_true_iff.
        rewrite In_nat_bool_app.
        apply orb_false_iff.
        split.
        -- apply andb_prop in Had1 as (nHin & _).
           apply negb_true_iff in nHin...
        -- apply negb_In_incr_all.
           apply andb_prop in Hal as (Hlt & _).
           apply Nat.ltb_lt...
      * apply andb_prop in Hal as (_ & Hal).
        apply andb_prop in Had1 as (_ & Had1).
        apply IHf1...
Qed.

Definition append_perm (f1 f2 : Perm) :=
  existT (fun l => is_perm l = true) (projT1 f1 ++ (incr_all (projT1 f2) (length (projT1 f1)))) (append_perm_is_perm (projT1 f1) (projT1 f2) (projT2 f1) (projT2 f2)).

Lemma app_nat_fun_vs_cons {A} : forall l1 l2 (a : A) n p
                                       (Hlen : length (n :: p) = length l2)
                                       (Hperm : is_perm (n :: p) = true)
                                       (Heq : a :: l1 = app_nat_fun l2 (n :: p)),
    {' (la , lb) : _ & prod (length la = n) (l2 = la ++ a :: lb)}.
Proof with try reflexivity; try assumption.
  intros l1 l2 a n p Hlen Hperm Heq.
  destruct l2; try now inversion Heq.
  unfold app_nat_fun in Heq.
  inversion Heq.
  change (match n with
           | 0 => a0
           | S n => nth l2 a0 n
           end) with (nth (a0 :: l2) a0 n) in H0.
  change (match n with
           | 0 => a0
           | S n => nth l2 a0 n
          end) with (nth (a0 :: l2) a0 n).
  apply nth_decomp.
  rewrite<- Hlen.
  apply andb_prop in Hperm as (Halt & _).
  apply andb_prop in Halt as (Hlt & _).
  apply Nat.ltb_lt in Hlt...
Qed.

Lemma app_perm_length {A} : forall (l : list A) p,
    length (projT1 p) = length l ->
    length (app_perm l p) = length l.
Proof with try reflexivity.
  destruct l...
  destruct p as (f & Hp).
  simpl.
  intros Hlen.
  rewrite map_length.
  apply Hlen.
Qed.

Lemma perm_has_inv : forall p,
    is_perm p = true ->
    { p_inv & prod (app_nat_fun p p_inv = Id (length p)) (prod (is_perm p_inv = true) (length p = length p_inv)) }.
Proof with try reflexivity; try assumption.
  intro p.
  remember (length p).
  revert p Heqn.
  induction n; intros p Heqn Hperm.
  { destruct p; try now inversion Heqn.
    split with nil.
    split; [ | split]... }
  assert (0 < length p) as H.
  { rewrite<- Heqn.
    lia. }
  destruct (perm_surj p 0 0 Hperm H) as (n0 & (Hlen & Heq)).
  assert (n = length (downshift p 0)).
  { destruct p; try now inversion H.
    simpl in Heqn.
    apply Nat.succ_inj in Heqn.
    rewrite Heqn.
    symmetry.
    apply downshift_perm_length... }
  specialize (IHn (downshift p 0) H0 (downshift_perm _ _ Hperm)) as (p_inv & (Heq' & (Hperm' & Heq_len))).
  apply andb_prop in Hperm' as (Hal & Had).
  split with (n0 :: (shift p_inv n0)).
  simpl.
  destruct p; try now inversion H.
  app_nat_fun_unfold p (shift p_inv n0) n1 n0.
  replace (nth (n1 :: p) n1 n0) with 0.
  2:{ symmetry.
      transitivity (nth (n1 :: p) 0 n0)...
      apply nth_correct... }
  split; [ | split].
  - replace (incr_all (Id n) 1) with (app_nat_fun (n1 :: p) (shift p_inv n0))...
    rewrite <- Heq'.
    pattern 0 at 1.
    rewrite <- Heq.
    rewrite app_nat_fun_downshift_shift...
    + rewrite Heq.
      rewrite incr_all_downshift_0...
      rewrite <- Heq.
      apply In_nat_bool_shift_false...
      * rewrite<- downshift_perm_length with _ 0...
        rewrite<- H0.
        rewrite Heq_len...
      * apply andb_prop in Hperm as (_ & Had')...
    + apply andb_prop in Hperm as (_ & Had')...
    + rewrite<- downshift_perm_length with _ 0...
      rewrite<- H0.
      rewrite Heq_len...
  - unfold is_perm; simpl; splitb; splitb.
    + apply Nat.ltb_lt.
      rewrite shift_length.
      lia.
    + rewrite shift_length.
      rewrite<- shift_all_lt...
      apply Nat.leb_le.
      lia.
    + assert (forall l k,
                 In_nat_bool k (shift l k) = false) as not_In_nat_bool_shift.
      { clear.
        induction l; intros k...
        simpl.
        case_eq (a <? k); intros Hlt.
        - simpl.
          replace (k =? a) with false; [apply IHl | ].
          symmetry.
          apply Nat.eqb_neq.
          apply Nat.ltb_lt in Hlt.
          lia.
        - simpl.
          replace (k =? (S a)) with false; [apply IHl | ].
          symmetry.
          apply Nat.eqb_neq.
          apply Nat.ltb_nlt in Hlt.
          lia. }
      apply negb_true_iff.
      apply not_In_nat_bool_shift...        
    + apply shift_keep_all_distinct...
  - rewrite shift_length.
    rewrite Heq_len...
Qed.

Lemma app_cperm_eq {A} : forall (l l' : list A),
    app_perm (l ++ l') (cperm (length l) (length l')) = l' ++ l.
Proof with try reflexivity.
  intros l l'.
  unfold cperm, app_perm , cfun; simpl.
  rewrite app_nat_fun_app.
  rewrite app_nat_fun_right.
  2:{ apply all_lt_Id. }
  rewrite app_Id.
  rewrite app_nat_fun_left.
  2:{ apply all_lt_Id. }
  rewrite app_Id...
Qed.

Lemma app_nat_fun_map {A B} : forall (f : A -> B) l p,
    app_nat_fun (map f l) p = map f (app_nat_fun l p).
Proof with try reflexivity.
  intros f l p.
  destruct l...
  induction p...
  rewrite map_cons.
  app_nat_fun_unfold (map f l) p (f a) a0.
  rewrite<- ? map_cons.
  rewrite IHp.
  app_nat_fun_unfold l p a a0.
  change ( map f (nth (a :: l) a a0 :: app_nat_fun (a :: l) p)) with (f (nth (a :: l) a a0) :: map f (app_nat_fun (a :: l) p)).
  rewrite map_nth...
Qed.

Lemma app_perm_map {A B} : forall (f : A -> B) l p,
    app_perm (map f l) p = map f (app_perm l p).
Proof with try reflexivity.
  intros f l (p & Hperm).
  unfold app_perm; simpl.
  apply app_nat_fun_map...
Qed.


  