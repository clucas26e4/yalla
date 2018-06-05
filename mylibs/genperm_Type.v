(* genperm Library *)

(* with output in Type *)

(** * Factorized statements for different notions of permutation *)

Require Import CMorphisms.
Require Import List.

Require Import Injective.
Require Import List_Type.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import CyclicPerm_Type.
Require Import CPermutation_Type_solve.



(** ** Definitions
 parametrized by a boolean. *)

(** Permutation or cyclic permutation *)
Definition PCperm_Type {A} (b : bool) :=
  if b then @Permutation_Type A else @CPermutation_Type A.

(** Permutation or equality *)
Definition PEperm_Type {A} (b : bool) :=
  if b then @Permutation_Type A else @eq (list A).


(** ** Permutation or cyclic permutation *)

(** unfolding into [Permutation] or [CPermutation] *)
Ltac hyps_PCperm_Type_unfold :=
  match goal with
  | H : PCperm_Type _ _ _ |- _ => unfold PCperm_Type in H ; hyps_PCperm_Type_unfold
  | _ => idtac
  end.

(** automatic solving *)
Ltac PCperm_Type_solve :=
  hyps_PCperm_Type_unfold ;
  simpl ;
  match goal with
  | |- PCperm_Type ?b _ _ => unfold PCperm_Type ; destruct b ;
                        simpl ; PCperm_Type_solve
  | |- Permutation_Type _ _  => perm_Type_solve
  | |- CPermutation_Type _ _  => cperm_Type_solve
  end.

(** *** Properties *)

Instance PCperm_perm_Type {A} b : Proper (PCperm_Type b ==> (@Permutation_Type A)) id.
Proof with try assumption.
destruct b ; intros l l' HP...
apply cperm_perm_Type...
Qed.

Instance cperm_PCperm_Type {A} b : Proper (CPermutation_Type ==> PCperm_Type b) (@id (list A)).
Proof with try assumption.
destruct b ; intros l l' HC...
apply cperm_perm_Type...
Qed.

Instance PCperm_Type_refl {A} b : Reflexive (@PCperm_Type A b).
Proof.
destruct b ; intros l.
- apply Permutation_Type_refl.
- apply cperm_Type_refl.
Qed.

Instance PCperm_Type_sym {A} b : Symmetric (@PCperm_Type A b).
Proof with try assumption.
destruct b ; intros l l' H.
- apply Permutation_Type_sym...
- apply cperm_Type_sym...
Qed.

Instance PCperm_Type_trans {A} b : Transitive (@PCperm_Type A b).
Proof with try eassumption.
destruct b ; intros l l' l'' H1 H2.
- eapply Permutation_Type_trans...
- eapply cperm_Type_trans...
Qed.

Instance PCperm_Type_equiv {A} b : Equivalence (@PCperm_Type A b).
Proof.
split.
- apply PCperm_Type_refl.
- apply PCperm_Type_sym.
- apply PCperm_Type_trans.
Qed.

Lemma PCperm_Type_swap {A} b : forall a1 a2 : A,
  PCperm_Type b (a1 :: a2 :: nil) (a2 :: a1 :: nil).
Proof.
destruct b ; intros.
- apply Permutation_Type_swap.
- apply cperm_Type_swap.
Qed.

Lemma PCperm_Type_last {A} b : forall (a : A) l,
  PCperm_Type b (a :: l) (l ++ a :: nil).
Proof.
destruct b ; intros ;
  rewrite <- (app_nil_l l) ; rewrite app_comm_cons.
- apply Permutation_Type_cons_append.
- apply cperm_Type_last.
Qed.

Lemma PCperm_Type_app_comm {A} b : forall l l',
  @PCperm_Type A b (l ++ l') (l' ++ l).
Proof.
destruct b ; intros.
- apply Permutation_Type_app_comm.
- apply cperm_Type.
Qed.

Lemma PCperm_Type_app_rot {A} b : forall l1 l2 l3,
  @PCperm_Type A b  (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof.
destruct b ; intros.
- apply Permutation_Type_app_rot.
- apply cperm_Type_app_rot.
Qed.

Lemma PCperm_Type_nil {A} b : forall l,
  @PCperm_Type A b nil l -> l = nil.
Proof with try assumption.
destruct b ; intros.
- apply Permutation_Type_nil...
- apply cperm_Type_nil...
Qed.

Lemma PCperm_Type_nil_cons {A} b : forall l (a : A),
  PCperm_Type b nil (a :: l) -> False.
Proof with try eassumption.
destruct b ; intros.
- eapply Permutation_Type_nil_cons...
- eapply cperm_Type_nil_cons...
Qed.

Lemma PCperm_Type_length_1_inv {A} b : forall (a : A) l,
  PCperm_Type b (a :: nil) l -> l = a :: nil.
Proof with try assumption.
destruct b ; intros.
- apply Permutation_Type_length_1_inv...
- apply cperm_Type_one_inv...
Qed.

Lemma PCperm_Type_length_2_inv {A} b : forall (a1 : A) a2 l,
  PCperm_Type b (a1 :: a2 :: nil) l -> { l = a1 :: a2 :: nil } + { l = a2 :: a1 :: nil }.
Proof with try assumption.
destruct b ; intros.
- apply Permutation_Type_length_2_inv...
- apply cperm_Type_two_inv...
Qed.

Lemma PCperm_Type_vs_elt_inv {A} b : forall (a : A) l l1 l2,
  PCperm_Type b l (l1 ++ a :: l2) ->
  { ll : { pl | l = fst pl ++ a :: snd pl } & PEperm_Type b (l2 ++ l1) (snd (proj1_sig ll) ++ fst (proj1_sig ll)) }.
Proof with try reflexivity.
destruct b ; intros a l l1 l2 HC.
- assert (Heq := HC).
  apply Permutation_Type_vs_elt_inv in Heq.
  destruct Heq as ((l' & l'') & Heq) ; subst.
  eapply (existT _ (exist _ (l',l'') _)).
  simpl in HC ; simpl.
  apply Permutation_Type_app_inv in HC.
  apply Permutation_Type_sym in HC.
  eapply Permutation_Type_trans ; [ eapply Permutation_Type_app_comm | ].
  eapply Permutation_Type_trans ; [ eassumption | ].
  apply Permutation_Type_app_comm.
  Unshelve. reflexivity.
- apply cperm_Type_vs_elt_inv in HC.
  destruct HC as ((l' & l'') & Heq1 & Heq2) ; subst.
  eapply (existT _ (exist _ (l',l'') _)).
  assumption.
  Unshelve. reflexivity.
Qed.

Lemma PCperm_Type_vs_cons_inv {A} b : forall (a : A) l l1,
  PCperm_Type b l (a :: l1) ->
  { ll : { pl | l = fst pl ++ a :: snd pl } & PEperm_Type b l1 (snd (proj1_sig ll) ++ fst (proj1_sig ll)) }.
Proof.
intros a l l1 HP.
rewrite <- app_nil_l in HP.
apply PCperm_Type_vs_elt_inv in HP.
destruct HP as (((l' & l'') & HP) & Heq) ; subst.
eapply (existT _ (exist _ (l',l'') _)).
simpl in Heq ; simpl.
rewrite app_nil_r in Heq.
assumption.
Unshelve. reflexivity.
Qed.

Instance PCperm_Type_map {A B} (f : A -> B) b :
  Proper (PCperm_Type b ==> PCperm_Type b) (map f).
Proof with try assumption.
destruct b ; intros l1 l2 HC.
- apply Permutation_Type_map...
- apply cperm_Type_map...
Qed.

Lemma PCperm_Type_map_inv {A B} b : forall (f : A -> B) l1 l2,
  PCperm_Type b l1 (map f l2) ->
  { l : _ & l1 = map f l & (PCperm_Type b l2 l) }.
Proof.
destruct b ; intros.
- eapply Permutation_Type_map_inv ; eassumption.
- eapply cperm_Type_map_inv ; eassumption.
Qed.

Instance PCperm_Type_in {A} b (a : A) : Proper (PCperm_Type b ==> Basics.impl) (In a).
Proof with try eassumption.
destruct b ; intros l l' HP HIn.
- eapply Permutation_Type_in...
- eapply cperm_Type_in...
Qed.

Instance PCperm_Type_Forall {A} b (P : A -> Prop) :
  Proper (PCperm_Type b ==> Basics.impl) (Forall P).
Proof with try eassumption.
destruct b ; intros l1 l2 HP HF.
- eapply Permutation_Type_Forall...
- eapply cperm_Type_Forall...
Qed.

Instance PCperm_Type_Exists {A} b (P : A -> Prop) :
  Proper (PCperm_Type b ==> Basics.impl) (Exists P).
Proof with try eassumption.
destruct b ; intros l1 l2 HP HE.
- eapply Permutation_Type_Exists...
- eapply cperm_Type_Exists...
Qed.

Instance PCperm_Type_Forall_Type {A} b (P : A -> Type) :
  Proper (PCperm_Type b ==> Basics.arrow) (Forall_Type P).
Proof with try eassumption.
destruct b ; intros l1 l2 HP HF.
- eapply Permutation_Type_Forall_Type...
- eapply cperm_Type_Forall_Type...
Qed.

Instance PCperm_Type_Exists_Type {A} b (P : A -> Type) :
  Proper (PCperm_Type b ==> Basics.arrow) (Exists_Type P).
Proof with try eassumption.
destruct b ; intros l1 l2 HP HE.
- eapply Permutation_Type_Exists_Type...
- eapply cperm_Type_Exists_Type...
Qed.

Lemma PCperm_Type_Forall2 {A B} b (P : A -> B -> Type) :
  forall l1 l1' l2, PCperm_Type b l1 l1' -> Forall2_Type P l1 l2 -> 
    { l2' : _ & PCperm_Type b l2 l2' & Forall2_Type P l1' l2' }.
Proof.
destruct b ; [ apply Permutation_Type_Forall2 | apply cperm_Type_Forall2 ].
Qed.

Lemma PCperm_Type_image {A B} b : forall (f : A -> B) a l l',
  PCperm_Type b (a :: l) (map f l') -> { a' | a = f a' }.
Proof with try eassumption.
destruct b ; intros.
- eapply Permutation_Type_image...
- eapply cperm_Type_image...
Qed.


(** ** Permutation or equality *)

(** unfolding into [Permutation] or [eq] and automatic solving *)
Ltac hyps_PEperm_Type_unfold :=
  match goal with
  | H : PEperm_Type _ _ _ |- _ => unfold PEperm_Type in H ; hyps_PEperm_Type_unfold
  | _ => idtac
  end.

(** automatic solving *)
Ltac PEperm_Type_solve :=
  hyps_PEperm_Type_unfold ;
  simpl ;
  match goal with
  | |- PEperm_Type ?b _ _ => unfold PEperm_Type ; destruct b ;
                        simpl ; PEperm_Type_solve
  | |- Permutation_Type _ _  => perm_Type_solve
  | |- eq _ _  => reflexivity
  end.

(** *** Properties *)

Instance PEperm_perm_Type {A} b : Proper (PEperm_Type b ==> (@Permutation_Type A)) id.
Proof.
destruct b ; intros l l' HP ; simpl in HP ; now subst.
Qed.

Instance PEperm_Type_refl {A} b : Reflexive (@PEperm_Type A b).
Proof.
destruct b ; intros l.
- apply Permutation_Type_refl.
- reflexivity.
Qed.

Instance PEperm_Type_sym {A} b : Symmetric (@PEperm_Type A b).
Proof with try assumption.
destruct b ; intros l l' HP.
- apply Permutation_Type_sym...
- symmetry...
Qed.

Instance PEperm_Type_trans {A} b : Transitive (@PEperm_Type A b).
Proof with try eassumption.
destruct b ; intros l l' l'' HP1 HP2.
- eapply Permutation_Type_trans...
- etransitivity...
Qed.

Instance PEperm_Type_equiv {A} b : Equivalence (@PEperm_Type A b).
Proof.
split.
- apply PEperm_Type_refl.
- apply PEperm_Type_sym.
- apply PEperm_Type_trans.
Qed.

Instance eq_PEperm_Type {A} b : Proper (eq ==> PEperm_Type b) (@id (list A)).
Proof.
destruct b ; intros l l' Heq ; subst.
- apply Permutation_Type_refl.
- reflexivity.
Qed.

Instance PEperm_Type_cons {A} b :
  Proper (eq ==> PEperm_Type b ==> PEperm_Type b) (@cons A).
Proof.
destruct b ; intros x y Heq l1 l2 HP ; subst.
- now apply Permutation_Type_cons.
- now rewrite HP.
Qed.

Instance PEperm_Type_app {A} b : Proper (PEperm_Type b ==> PEperm_Type b ==> PEperm_Type b) (@app A).
Proof.
destruct b ; simpl ; intros l m HP1 l' m' HP2.
- now apply Permutation_Type_app.
- now subst.
Qed.

Lemma PEperm_Type_app_tail {A} b : forall l l' tl : list A,
  PEperm_Type b l l' -> PEperm_Type b (l ++ tl) (l' ++ tl).
Proof.
destruct b ; simpl ; intros l l' tl HP.
- now apply Permutation_Type_app_tail.
- now subst.
Qed.

Lemma PEperm_Type_app_head {A} b : forall l tl tl' : list A,
  PEperm_Type b tl tl' -> PEperm_Type b (l ++ tl) (l ++ tl').
Proof.
destruct b ; simpl ; intros l tl tl' HP.
- now apply Permutation_Type_app_head.
- now subst.
Qed.

Lemma PEperm_Type_add_inside {A} b : forall (a : A) l l' tl tl',
  PEperm_Type b l l' -> PEperm_Type b tl tl' -> PEperm_Type b (l ++ a :: tl) (l' ++ a :: tl').
Proof.
destruct b ; simpl ; intros a l l' tl tl' HP1 HP2.
- now apply Permutation_Type_add_inside.
- now subst.
Qed.

Lemma PEperm_Type_nil {A} b : forall l, @PEperm_Type A b nil l -> l = nil.
Proof with try assumption.
destruct b ; intros.
- apply Permutation_Type_nil...
- symmetry...
Qed.

Lemma PEperm_nil_cons {A} b : forall l (a : A),
  PEperm_Type b nil (a :: l) -> False.
Proof with try eassumption.
destruct b ; intros l a H.
- eapply Permutation_Type_nil_cons...
- inversion H.
Qed.

Lemma PEperm_Type_length_1_inv {A} b : forall (a : A) l,
  PEperm_Type b (a :: nil) l -> l = a :: nil.
Proof with try assumption.
destruct b ; intros.
- apply Permutation_Type_length_1_inv...
- symmetry...
Qed.

Lemma PEperm_Type_length_2_inv {A} b : forall (a1 : A) a2 l,
  PEperm_Type b (a1 :: a2 :: nil) l -> { l = a1 :: a2 :: nil } + { l = a2 :: a1 :: nil }.
Proof with try assumption.
destruct b ; intros.
- apply Permutation_Type_length_2_inv...
- left ; symmetry...
Qed.

Lemma PEperm_Type_vs_elt_inv {A} b : forall (a : A) l l1 l2,
  PEperm_Type b l (l1 ++ a :: l2) ->
  { ll : { pl | l = fst pl ++ a :: snd pl } & PEperm_Type b (l1 ++ l2) (fst (proj1_sig ll) ++ snd (proj1_sig ll)) }.
Proof.
destruct b ; simpl ; intros a l l1 l2 HP.
- assert (HP' := HP).
  apply Permutation_Type_vs_elt_inv in HP'.
  destruct HP' as ((l' & l'') & Heq) ; subst.
  apply Permutation_Type_app_inv in HP.
  apply Permutation_Type_sym in HP.
  eapply (existT _ (exist _ (l',l'') _)).
  assumption.
  Unshelve. reflexivity.
- subst.
  eapply (existT _ (exist _ (l1,l2) _)).
  reflexivity.
  Unshelve. reflexivity.
Qed.

Lemma PEperm_Type_vs_cons_inv {A} b : forall (a : A) l l1,
  PEperm_Type b l (a :: l1) ->
  { ll : { pl | l = fst pl ++ a :: snd pl } & PEperm_Type b l1 (fst (proj1_sig ll) ++ snd (proj1_sig ll)) }.
Proof.
intros a l l1 HP.
rewrite <- (app_nil_l l1).
eapply PEperm_Type_vs_elt_inv.
assumption.
Qed.

Instance PEperm_Type_in {A} b (a : A) : Proper (PEperm_Type b ==> Basics.impl) (In a).
Proof with try eassumption.
destruct b ; simpl ; intros l l' HP HIn.
- eapply Permutation_Type_in...
- subst...
Qed.

Instance PEperm_Type_Forall {A} b (P : A -> Prop) :
  Proper (PEperm_Type b ==> Basics.impl) (Forall P).
Proof with try eassumption.
destruct b ; simpl ; intros l1 l2 HP HF.
- eapply Permutation_Type_Forall...
- subst...
Qed.

Instance PEperm_Type_Exists {A} b (P : A -> Prop) :
  Proper (PEperm_Type b ==> Basics.impl) (Exists P).
Proof with try eassumption.
destruct b ; simpl ; intros l1 l2 HP HF.
- eapply Permutation_Type_Exists...
- subst...
Qed.

Lemma PEperm_Type_Forall2 {A B} b (P : A -> B -> Prop) :
  forall l1 l1' l2, PEperm_Type b l1 l1' -> Forall2_Type P l1 l2 -> 
    { l2' : _ & PEperm_Type b l2 l2' & Forall2_Type P l1' l2' }.
Proof.
destruct b ; [ apply Permutation_Type_Forall2 | ].
intros l1 l1' l2 HE HF ; simpl in HE ; subst.
exists l2 ; [ reflexivity | assumption ].
Qed.

Instance PEperm_Type_map {A B} (f : A -> B) b :
  Proper (PEperm_Type b ==> PEperm_Type b) (map f).
Proof.
destruct b ; intros l l' HP.
- apply Permutation_Type_map.
  assumption.
- simpl in HP ; subst.
  reflexivity.
Qed.

Lemma PEperm_Type_map_inv {A B} b : forall (f : A -> B) l1 l2,
  PEperm_Type b l1 (map f l2) ->
  { l : _ & l1 = map f l & (PEperm_Type b l2 l) }.
Proof.
destruct b ; simpl ; intros f l1 l2 HP.
- eapply Permutation_Type_map_inv ; eassumption.
- subst.
  exists l2 ; reflexivity.
Qed.

Instance PEperm_Type_rev {A} b : Proper (PEperm_Type b ==> PEperm_Type b) (@rev A).
Proof.
destruct b ; intros l1 l2 HP.
- now apply Permutation_Type_rev'.
- now (simpl in HP ; subst).
Qed.


(* TODO place elsewhere ??? *)
Require Import List_Type_more.
Lemma Permutation_Type_map_inv_inj {A B} : forall f : A -> B, injective f ->
  forall l1 l2, Permutation_Type (map f l1) (map f l2) -> Permutation_Type l1 l2.
Proof with try assumption.
intros f Hi l1 ; induction l1 ; intros l2 HP.
- apply Permutation_Type_nil in HP.
  destruct l2 ; inversion HP.
  apply Permutation_Type_refl.
- assert (Heq := HP).
  apply Permutation_Type_sym in Heq.
  apply Permutation_Type_vs_cons_inv in Heq.
  destruct Heq as ((l3 & l4) & Heq).
  symmetry in Heq.
  decomp_map_Type Heq ; subst.
  rewrite map_app in HP.
  simpl in HP.
  rewrite Heq3 in HP.
  apply Permutation_Type_cons_app_inv in HP.
  specialize IHl1 with (l0 ++ l6).
  rewrite map_app in IHl1.
  apply IHl1 in HP.
  apply Hi in Heq3 ; subst.
  apply Permutation_Type_cons_app...
Qed.

Lemma PEperm_Type_map_inv_inj {A B} b : forall f : A -> B, injective f ->
  forall l1 l2, PEperm_Type b (map f l1) (map f l2) -> PEperm_Type b l1 l2.
Proof with try assumption.
destruct b ; intros f Hi l1 l2 HP.
- apply Permutation_Type_map_inv_inj in HP...
- apply map_inj in HP...
Qed.

Lemma PEperm_Type_image {A B} b : forall (f : A -> B) a l l',
  PEperm_Type b (a :: l) (map f l') -> { a' | a = f a' }.
Proof.
destruct b ; intros f a l l' H.
- eapply Permutation_Type_image ; eassumption.
- destruct l' ; inversion H ; subst.
  exists a0 ; reflexivity.
Qed.


(** ** From PEperm to PCperm *)

Instance PEperm_PCperm_Type {A} b : Proper (PEperm_Type b ==> PCperm_Type b) (@id (list A)).
Proof.
destruct b ; simpl ; intros l l' HP.
- assumption.
- subst ; apply cperm_Type_refl.
Qed.

Instance PEperm_PCperm_Type_cons {A} b :
  Proper (eq ==> PEperm_Type b ==> PCperm_Type b) (@cons A).
Proof.
intros x y Heq l1 l2 HP ; subst.
apply PEperm_PCperm_Type.
now apply PEperm_Type_cons.
Qed.

Instance PEperm_PCperm_Type_app {A} b :
  Proper (PEperm_Type b ==> PEperm_Type b ==> PCperm_Type b) (@app A).
Proof.
intros l1 l1' HPhd l2 l2' HPtl.
apply PEperm_PCperm_Type.
rewrite HPhd.
rewrite HPtl.
reflexivity.
Qed.








