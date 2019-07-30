(* ll_prop library for yalla *)

(** * Properties relying on cut admissibility *)

Require Import Bool_more.
Require Import List_more.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import CyclicPerm_Type.
Require Import genperm_Type.
Require Import Dependent_Forall_Type.
Require Import flat_map_Type_more.

Require Export ll_cut.

(** Some additional reversibility statements *)
Lemma with_rev1_noax {P} : (projT1 (pgax P) -> False) ->
forall A B l1 l2, ll P (l1 ++ awith A B :: l2) -> ll P (l1 ++ A :: l2).
Proof with myeeasy.
intros Hgax A B l1 l2 pi.
assert (ll P (dual (awith A B) :: A :: nil)) as pi'.
{ apply plus_r1.
  eapply ex_r ; [ | apply PCperm_Type_swap ].
  apply ax_exp. }
eapply (ex_r _ ((l2 ++ l1) ++ A :: nil)) ; [ | PCperm_Type_solve ].
eapply cut_r_axfree ; try eassumption.
eapply ex_r ; [ apply pi | PCperm_Type_solve ].
Qed.

Lemma with_rev2_noax {P} : (projT1 (pgax P) -> False) ->
forall A B l1 l2, ll P (l1 ++ awith B A :: l2) -> ll P (l1 ++ A :: l2).
Proof with myeeasy.
intros Hgax A B l1 l2 pi.
assert (ll P (dual (awith B A) :: A :: nil)) as pi'.
{ apply plus_r2.
  eapply ex_r ; [ | apply PCperm_Type_swap ].
  apply ax_exp. }
eapply (ex_r _ ((l2 ++ l1) ++ A :: nil)) ; [ | PCperm_Type_solve ].
eapply cut_r_axfree ; try eassumption.
eapply ex_r ; [ apply pi | PCperm_Type_solve ].
Qed.

Lemma oc_rev_noax {P} : (projT1 (pgax P) -> False) ->
forall A l1 l2, ll P (l1 ++ oc A :: l2) -> ll P (l1 ++ A :: l2).
Proof with myeeasy.
intros Hgax A l1 l2 pi.
assert (ll P (dual (oc A) :: A :: nil)) as pi'.
{ apply de_r.
  eapply ex_r ; [ | apply PCperm_Type_swap ].
  apply ax_exp. }
eapply (ex_r _ ((l2 ++ l1) ++ A :: nil)) ; [ | PCperm_Type_solve ].
eapply cut_r_axfree ; try eassumption.
eapply ex_r ; [ apply pi | PCperm_Type_solve ].
Qed.



(** ** Subformula Property *)

(** version of ll with predicate parameter for constraining sequents *)
Inductive ll_ps P PS : list formula -> Type :=
| ax_ps_r : forall X, is_true (PS (covar X :: var X :: nil)) -> ll_ps P PS (covar X :: var X :: nil)
| ex_ps_r : forall l1 l2, is_true (PS l2) -> ll_ps P PS l1 -> PCperm_Type (pperm P) l1 l2 -> ll_ps P PS l2
| ex_wn_ps_r : forall l1 lw lw' l2, is_true (PS (l1 ++ map wn lw' ++ l2)) ->
                 ll_ps P PS (l1 ++ map wn lw ++ l2) ->
                 Permutation_Type lw lw' -> ll_ps P PS (l1 ++ map wn lw' ++ l2)
| mix_ps_r : forall L, pmix P (length L) = true -> is_true (PS (concat L)) ->
                       Forall_Type (ll_ps P PS) L ->
                       ll_ps P PS (concat L)
| one_ps_r : is_true (PS (one :: nil)) -> ll_ps P PS (one :: nil)
| bot_ps_r : forall l, is_true (PS (bot :: l)) -> ll_ps P PS l -> ll_ps P PS (bot :: l)
| tens_ps_r : forall A B l1 l2, is_true (PS (tens A B :: l2 ++ l1)) ->
                               ll_ps P PS (A :: l1) -> ll_ps P PS (B :: l2) ->
                               ll_ps P PS (tens A B :: l2 ++ l1)
| parr_ps_r : forall A B l, is_true (PS (parr A B :: l)) -> 
                               ll_ps P PS (A :: B :: l) -> ll_ps P PS (parr A B :: l)
| top_ps_r : forall l, is_true (PS (top :: l)) -> ll_ps P PS (top :: l)
| plus_ps_r1 : forall A B l, is_true (PS (aplus A B :: l)) ->
                               ll_ps P PS (A :: l)-> ll_ps P PS (aplus A B :: l)
| plus_ps_r2 : forall A B l, is_true (PS (aplus B A :: l)) ->
                               ll_ps P PS (A :: l) -> ll_ps P PS (aplus B A :: l)
| with_ps_r : forall A B l, is_true (PS (awith A B :: l)) ->
                               ll_ps P PS (A :: l) -> ll_ps P PS (B :: l) ->
                               ll_ps P PS (awith A B :: l)
| oc_ps_r : forall A l, is_true (PS (oc A :: map wn l)) ->
                                ll_ps P PS (A :: map wn l) -> ll_ps P PS (oc A :: map wn l)
| de_ps_r : forall A l, is_true (PS (wn A :: l)) -> ll_ps P PS (A :: l) -> ll_ps P PS (wn A :: l)
| wk_ps_r : forall A l, is_true (PS (wn A :: l)) -> ll_ps P PS l -> ll_ps P PS (wn A :: l)
| co_ps_r : forall A l, is_true (PS (wn A :: l)) ->
                            ll_ps P PS (wn A :: wn A :: l) -> ll_ps P PS (wn A :: l)
| cut_ps_r {f : pcut P = true} : forall A l1 l2, is_true (PS (l2 ++ l1)) ->
                               ll_ps P PS (dual A :: l1) -> ll_ps P PS (A :: l2) ->
                               ll_ps P PS (l2 ++ l1)
| gax_ps_r : forall a, is_true (PS (projT2 (pgax P) a)) -> ll_ps P PS (projT2 (pgax P) a).

Section ll_ps_ind.
  Variable P : pfrag.
  Variable PS : list formula -> bool.

  Definition Forall_Proofs_ps (Pred : forall l, ll_ps P PS l -> Type) {L} (piL : Forall_Type (ll_ps P PS) L) :=
    Dependent_Forall_Type Pred piL.

  Fixpoint ll_ps_nested_ind {l} (pi : ll_ps P PS l): forall (Pred : forall l, ll_ps P PS l -> Type),
    (forall X Hps, Pred (covar X :: var X :: nil) (ax_ps_r P PS X Hps)) ->
    (forall l1 l2 Hps pi p, Pred l1 pi -> Pred l2 (ex_ps_r P PS l1 l2 Hps pi p)) ->
    (forall l1 lw lw' l2 Hps pi p, Pred (l1 ++ map wn lw ++ l2) pi ->
      Pred (l1 ++ map wn lw' ++ l2) (ex_wn_ps_r P PS l1 lw lw' l2 Hps pi p)) ->
    (forall L eqpmix Hps PL, Forall_Proofs_ps Pred PL ->
      Pred (concat L) (mix_ps_r P PS L eqpmix Hps PL)) ->
    (forall Hps, Pred (one :: nil) (one_ps_r P PS Hps)) ->
    (forall l Hps pi, Pred l pi -> Pred (bot :: l) (bot_ps_r P PS l Hps pi)) ->
    (forall A B l1 l2 Hps pi1 pi2, Pred (A :: l1) pi1 -> Pred (B :: l2) pi2 ->
      Pred (tens A B :: l2 ++ l1) (tens_ps_r P PS A B l1 l2 Hps pi1 pi2)) ->
    (forall A B l Hps pi, Pred (A :: B :: l) pi -> Pred (parr A B :: l) (parr_ps_r P PS A B l Hps pi)) ->
    (forall l Hps, Pred (top :: l) (top_ps_r P PS l Hps)) ->
    (forall A B l Hps pi, Pred (A :: l) pi -> Pred (aplus A B :: l) (plus_ps_r1 P PS A B l Hps pi)) ->
    (forall A B l Hps pi, Pred (A :: l) pi -> Pred (aplus B A :: l) (plus_ps_r2 P PS A B l Hps pi)) ->
    (forall A B l Hps pi1 pi2, Pred (A :: l) pi1 -> Pred (B :: l) pi2 ->
      Pred (awith A B :: l) (with_ps_r P PS A B l Hps pi1 pi2)) ->
    (forall A l Hps pi, Pred (A :: map wn l) pi -> Pred (oc A :: map wn l) (oc_ps_r P PS A l Hps pi)) ->
    (forall A l Hps pi, Pred (A :: l) pi -> Pred (wn A :: l) (de_ps_r P PS A l Hps pi)) ->
    (forall A l Hps pi, Pred l pi -> Pred (wn A :: l) (wk_ps_r P PS A l Hps pi)) ->
    (forall A l Hps pi, Pred (wn A :: wn A :: l) pi -> Pred (wn A :: l) (co_ps_r P PS A l Hps pi)) ->
    (forall f A l1 l2 Hps pi1 pi2, Pred (dual A :: l1) pi1 -> Pred (A :: l2) pi2 ->
      Pred (l2 ++ l1) (@cut_ps_r P PS f A l1 l2 Hps pi1 pi2)) ->
    (forall a Hps, Pred (projT2 (pgax P) a) (gax_ps_r P PS a Hps)) ->
    Pred l pi :=
      fun Pred ax_case ex_case ex_wn_case mix_case one_case bot_case tens_case parr_case
               top_case plus_case1 plus_case2 with_case oc_case de_case wk_case co_case cut_case gax_case =>
    let rec_call {l} (pi : ll_ps P PS l) :=
       (ll_ps_nested_ind pi Pred ax_case ex_case ex_wn_case mix_case one_case bot_case tens_case parr_case
                                 top_case plus_case1 plus_case2 with_case
                                 oc_case de_case wk_case co_case cut_case gax_case) in
    match pi with
    | ax_ps_r _ _ X Hps => ax_case X Hps
    | ex_ps_r _ _ l1 l2 Hps pi p => ex_case l1 l2 Hps pi p (rec_call pi)
    | ex_wn_ps_r _ _ l1 lw lw' l2 Hps pi p => ex_wn_case l1 lw lw' l2 Hps pi p (rec_call pi)
    | mix_ps_r _ _ L eqpmix Hps PL => mix_case L eqpmix Hps PL (
        (fix ll_ps_nested_ind_aux L (PL : Forall_Type (ll_ps P PS) L) : Forall_Proofs_ps Pred PL :=
          match PL with
          | Forall_Type_nil _ => Dependent_Forall_Type_nil Pred
          | @Forall_Type_cons _ _ l L Pil PiL => Dependent_Forall_Type_cons Pred l Pil PiL (rec_call Pil)
                                                                            (ll_ps_nested_ind_aux L PiL)
          end) L PL)
    | one_ps_r _ _ Hps => one_case Hps
    | bot_ps_r _ _ l Hps pi => bot_case l Hps pi (rec_call pi)
    | tens_ps_r _ _ A B l1 l2 Hps pi1 pi2 => tens_case A B l1 l2 Hps pi1 pi2 (rec_call pi1) (rec_call pi2)
    | parr_ps_r _ _ A B l Hps pi => parr_case A B l Hps pi (rec_call pi)
    | top_ps_r _ _ l Hps => top_case l Hps
    | plus_ps_r1 _ _ A B l Hps pi => plus_case1 A B l Hps pi (rec_call pi)
    | plus_ps_r2 _ _ A B l Hps pi => plus_case2 A B l Hps pi (rec_call pi)
    | with_ps_r _ _ A B l Hps pi1 pi2 => with_case A B l Hps pi1 pi2 (rec_call pi1) (rec_call pi2)
    | oc_ps_r _ _ A l Hps pi => oc_case A l Hps pi (rec_call pi)
    | de_ps_r _ _ A l Hps pi => de_case A l Hps pi (rec_call pi)
    | wk_ps_r _ _ A l Hps pi => wk_case A l Hps pi (rec_call pi)
    | co_ps_r _ _ A l Hps pi => co_case A l Hps pi (rec_call pi)
    | @cut_ps_r _ _ f A l1 l2 Hps pi1 pi2 => cut_case f A l1 l2 Hps pi1 pi2 (rec_call pi1) (rec_call pi2)
    | gax_ps_r _ _ a Hps => gax_case a Hps
    end.

End ll_ps_ind.

Lemma stronger_ps_pfrag P Q : le_pfrag P Q -> forall PS l,
  ll_ps P PS l -> ll_ps Q PS l.
Proof with myeeasy.
intros Hle PS l H.
induction H using (ll_ps_nested_ind P PS) ; try (econstructor ; myeeasy ; fail).
- apply (ex_ps_r _ _ l1)...
  destruct Hle as (_ & _ & _  & Hp).
  unfold PCperm_Type in p.
  unfold PCperm_Type.
  destruct (pperm P) ; destruct (pperm Q) ;
    simpl in Hp ; try inversion Hp...
  apply cperm_perm_Type...
- unfold le_pfrag in Hle.
  destruct Hle as (_ & _ & Hmix & _).
  specialize (Hmix (length L)).
  rewrite eqpmix in Hmix.
  simpl in Hmix...
  apply mix_ps_r...
  apply forall_Forall_Type.
  intros l' Hin.
  apply(In_Forall_Type_in _ _ _ PL) in Hin as (pi & Hin).
  refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin).
- destruct Hle as [Hle _].
  rewrite f in Hle.
  simpl in Hle.
  eapply (@cut_ps_r _ _ Hle)...
- destruct Hle as (_ & Hgax & _).
  destruct (Hgax a) as [b Heq].
  rewrite Heq in Hps ; rewrite Heq.
  apply gax_ps_r...
Qed.

Lemma ll_ps_stronger {P} : forall PS QS l,
  ll_ps P PS l -> (forall x, is_true (PS x) -> is_true (QS x)) -> ll_ps P QS l.
Proof with try eassumption.
intros PS QS l pi Hs.
induction pi using (ll_ps_nested_ind P PS) ; try (econstructor ; try apply Hs ; eassumption ; fail).
apply mix_ps_r ; [ | apply Hs | ]...
apply forall_Forall_Type.
intros l' Hin.
apply(In_Forall_Type_in _ _ _ PL) in Hin as (pi & Hin).
refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin).
Qed.

Lemma ll_ps_is_ps {P} : forall l PS, ll_ps P PS l -> is_true (PS l).
Proof.
intros l PS Hll; inversion Hll ; assumption.
Qed.

Lemma ll_ps_is_ll {P} : forall l PS, ll_ps P PS l -> ll P l.
Proof with try eassumption.
intros l PS pi.
induction pi using (ll_ps_nested_ind P PS); try (econstructor ; eassumption ; fail).
apply mix_r...
apply forall_Forall_Type.
intros l' Hin.
apply(In_Forall_Type_in _ _ _ PL) in Hin as (pi & Hin).
refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin).
Qed.

Lemma ll_is_ll_ps {P} : forall l, ll P l -> ll_ps P (fun _ => true) l.
Proof with myeeasy.
intros l pi.
induction pi using (ll_nested_ind P); try (econstructor ; myeeasy ; fail).
apply mix_ps_r...
apply forall_Forall_Type.
intros l' Hin.
apply(In_Forall_Type_in _ _ _ PL) in Hin as (pi & Hin).
refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin).
Qed.

(** A fragment is a subset of formulas closed under subformula. *)
Definition fragment FS :=
  forall A, is_true (FS A) -> forall B, subform B A -> is_true (FS B).

(** Linear logic is conservative over its fragments (in the absence of cut). *)

Lemma conservativity {P} : pcut P = false -> forall FS, fragment FS ->
  forall l, ll_ps P (fun _ => true) l -> is_true (Forallb FS l) -> ll_ps P (Forallb FS) l.
Proof with try eassumption ; try reflexivity.
intros P_cutfree FS HFS l pi.
induction pi using (ll_ps_nested_ind P (fun _ => true)) ; intros HFrag.
- apply ax_ps_r...
- apply (ex_ps_r _ _ l1)...
  apply IHpi.
  apply PCperm_Type_sym in p.
  apply Forallb_Forall in HFrag.
  apply Forallb_Forall.
  eapply PCperm_Type_Forall...
- eapply ex_wn_ps_r...
  apply IHpi.
  apply Forallb_Forall in HFrag.
  apply Forallb_Forall.
  apply (Permutation_Type_map wn) in p.
  eapply Permutation_Type_Forall...
  PCperm_Type_solve.
- apply Forallb_Forall in HFrag.
  apply mix_ps_r...
  + apply Forallb_Forall...
  + apply forall_Forall_Type.
    intros l' Hin.
    apply(In_Forall_Type_in _ _ _ PL) in Hin as (pi & Hin).
    refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin _).
    clear - Hin HFrag.
    apply Forallb_Forall.
    apply Forall_forall.
    intros A Hin'.
    apply (Forall_forall (fun x => is_true (FS x)) (concat L))...
    apply in_concat with l'...
    apply In_Forall_Type_to_In_Type in Hin.
    apply In_Type_to_In in Hin...
- apply one_ps_r...
- apply bot_ps_r...
  inversion HFrag.
  apply andb_true_iff in H0.
  destruct H0.
  apply IHpi...
- assert (HFrag2 := HFrag).
  simpl in HFrag.
  apply andb_true_iff in HFrag.
  destruct HFrag as [HFragt HFrag].
  apply Forallb_Forall in HFrag.
  apply Forall_app_inv in HFrag.
  destruct HFrag as [HFragl HFragr].
  apply Forallb_Forall in HFragl.
  apply Forallb_Forall in HFragr.
  apply tens_ps_r...
  + apply IHpi1...
    simpl ; apply andb_true_iff ; split...
    eapply HFS...
    apply sub_tens_l...
  + apply IHpi2...
    simpl ; apply andb_true_iff ; split...
    eapply HFS...
    apply sub_tens_r...
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply parr_ps_r...
  apply IHpi.
  simpl ; apply andb_true_iff ; split ;
    [ | simpl ; apply andb_true_iff ; split ]...
  + eapply HFS...
    apply sub_parr_l...
  + eapply HFS...
    apply sub_parr_r...
- apply top_ps_r...
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply plus_ps_r1...
  apply IHpi.
  simpl ; apply andb_true_iff ; split...
  eapply HFS...
  apply sub_plus_l...
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply plus_ps_r2...
  apply IHpi.
  simpl ; apply andb_true_iff ; split...
  eapply HFS...
  apply sub_plus_r...
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply with_ps_r...
  + apply IHpi1...
    simpl ; apply andb_true_iff ; split...
    eapply HFS...
    apply sub_with_l...
  + apply IHpi2...
    simpl ; apply andb_true_iff ; split...
    eapply HFS...
    apply sub_with_r...
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply oc_ps_r...
  apply IHpi.
  simpl ; apply andb_true_iff ; split...
  eapply HFS...
  apply sub_oc...
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply de_ps_r...
  apply IHpi.
  simpl ; apply andb_true_iff ; split...
  eapply HFS...
  apply sub_wn...
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply wk_ps_r...
  apply IHpi...
- inversion HFrag ; subst.
  apply andb_true_iff in H0 ; destruct H0.
  apply co_ps_r...
  apply IHpi.
  simpl ; apply andb_true_iff ; split...
- rewrite P_cutfree in f.
  inversion f.
- apply gax_ps_r...
Qed.

(** Subformula property:
any provable sequent is provable by a proof containing only subformulas of this sequent. *)
Proposition subformula {P} : pcut P = false -> forall l,
  ll P l -> ll_ps P (fun x => subformb_list x l) l.
Proof with try eassumption ; try reflexivity.
intros P_cutfree l pi.
apply ll_is_ll_ps in pi.
apply conservativity...
- intros A Hf B Hs.
  revert Hf ; clear - Hs ; induction l ; intro Hf ; inversion Hf ; subst.
  simpl ; apply orb_true_iff.
  apply orb_true_iff in H0.
  destruct H0.
  + left; eapply subb_trans...
    apply subb_sub...
  + right; apply IHl...
- apply (subb_id_list l nil).
Qed.

(* Cut is admissible in any fragment with no axioms. *)
Lemma cut_admissible_fragment_axfree {P} : (projT1 (pgax P) -> False) ->
 forall FS, fragment FS -> forall l,
   ll_ps P (Forallb FS) l -> ll_ps (cutrm_pfrag P) (Forallb FS) l.
Proof with myeeasy.
intros P_axfree FS HFS l pi.
apply conservativity...
- apply ll_is_ll_ps.
  apply cut_admissible_axfree...
  eapply ll_ps_is_ll...
- destruct pi...
Qed.

(** Linear logic (with no axioms) is conservative over its fragments. *)
Lemma conservativity_axfree {P} : (projT1 (pgax P) -> False) ->
  forall FS, fragment FS -> forall l,
    ll P l -> is_true (Forallb FS l) -> ll_ps P (Forallb FS) l.
Proof with try eassumption ; try reflexivity.
intros P_axfree FS Hf l pi HFS.
apply cut_admissible_axfree in pi...
apply ll_is_ll_ps in pi.
eapply conservativity in pi...
clear - pi ; induction pi using (ll_ps_nested_ind (cutrm_pfrag P) (Forallb FS));
  try (econstructor ; eassumption ; fail).
- simpl in eqpmix.
  apply mix_ps_r...
  apply forall_Forall_Type.
  intros l' Hin.
  apply (In_Forall_Type_in _ _ _ PL) in Hin as (pi & Hin).
  refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hin).
- eapply @cut_ps_r...
  destruct P.
  inversion f.
- revert a Hps.
  assert (pgax (cutrm_pfrag P) = pgax P) as Hcut by reflexivity.
  rewrite Hcut.
  apply gax_ps_r.
Qed.


(** ** Deduction Theorem *)

(** Deduction lemma for linear logic. *)
Lemma deduction_list {P} : pperm P = true -> pcut P = true -> forall lax l, 
  ll (axupd_pfrag P (existT (fun x => x -> list formula) (sum _ { k | k < length lax })
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr x => nth (proj1_sig x) lax one :: nil
                                          end))) l
  -> ll P (l ++ map wn (map dual lax)).
Proof with myeeasy.
intros P_perm P_cut lax.
induction lax ; intros l pi.
- list_simpl.
  eapply stronger_pfrag...
  nsplit 4...
  simpl ; intros a.
  destruct a.
  + exists p...
  + exfalso ; destruct s as [k Hlt] ; inversion Hlt.
- remember (axupd_pfrag P (existT (fun x => x -> list formula) (sum _ { k | k < length lax })
                                  (fun a => match a with
                                            | inl x => projT2 (pgax P) x
                                            | inr x => nth (proj1_sig x) lax one :: nil
                                            end)))
    as Q.
  simpl; cons2app; rewrite app_assoc.
  apply IHlax.
  eapply (@ext_wn _ _ _ (dual a :: nil)) in pi.
  eapply ax_gen ; [ | | | | apply pi ] ; try (now rewrite HeqQ).
  simpl in pi ; simpl ; intros a0.
  destruct a0.
  + eapply ex_r ; [ | apply PCperm_Type_last ].
    apply wk_r.
    assert ({ b | projT2 (pgax P) p = projT2 (pgax Q) b}) as [b Hgax]
      by (subst ; simpl ; exists (inl p) ; reflexivity).
    rewrite Hgax.
    apply gax_r.
  + destruct s as [k Hlen].
    destruct k ; simpl.
    * eapply ex_r ; [ | apply PCperm_Type_swap ].
      apply de_r.
      eapply ex_r ; [ | apply PCperm_Type_swap ].
      apply ax_exp.
    * eapply ex_r ; [ | apply PCperm_Type_swap ].
      apply wk_r.
      assert ({ b | nth k lax one :: nil = projT2 (pgax Q) b}) as [b Hgax].
      { subst ; simpl ; clear - Hlen.
        apply Lt.lt_S_n in Hlen.
        exists (inr (exist _ k Hlen))... }
      rewrite Hgax.
      apply gax_r.
Unshelve. assumption.
Qed.

Lemma deduction_list_inv {P} : pperm P = true -> pcut P = true -> forall lax l, 
  ll P (l ++ map wn (map dual lax)) ->
  ll (axupd_pfrag P (existT (fun x => x -> list formula) (sum _ { k | k < length lax })
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr x => nth (proj1_sig x) lax one :: nil
                                          end))) l.
Proof with myeeasy.
intros P_perm P_cut lax.
induction lax ; intros l pi.
- list_simpl in pi.
  eapply stronger_pfrag...
  nsplit 4...
  simpl ; intros a.
  exists (inl a)...
- list_simpl in pi.
  cons2app in pi.
  rewrite app_assoc in pi.
  apply IHlax in pi.
  rewrite <- (app_nil_r l).
  eapply (cut_r _ (wn (dual a)))...
  + simpl ; rewrite bidual.
    change nil with (map wn nil).
    apply oc_r ; simpl.
    assert ({ b | a :: nil = projT2 (pgax (axupd_pfrag P
     (existT (fun x => x -> list formula) (sum _ {k | k < S (length lax)})
        (fun a0 => match a0 with
                   | inl x => projT2 (pgax P) x
                   | inr x => match proj1_sig x with
                              | 0 => a
                              | S m => nth m lax one
                              end :: nil
                   end)))) b}) as [b Hgax]
      by (clear ; simpl ; exists (inr (exist _ 0 (le_n_S _ _ (le_0_n _)))) ; reflexivity).
    rewrite Hgax.
    apply gax_r.
  + eapply ex_r ; [ | apply PCperm_Type_sym ; apply PCperm_Type_last ].
    eapply stronger_pfrag...
    nsplit 4...
    simpl ; intros a'.
    destruct a'.
    * exists (inl p)...
    * destruct s as [k Hlen] ; simpl.
      apply Lt.lt_n_S in Hlen.
      exists (inr (exist _ (S k) Hlen))...
Unshelve. assumption.
Qed.

Lemma deduction {P} : pperm P = true -> (projT1 (pgax P) -> False) -> pcut P = true -> forall lax l,
  ll (axupd_pfrag P (existT (fun x => x -> list formula) { k | k < length lax }
                            (fun a => nth (proj1_sig a) lax one :: nil))) l
    -> ll (cutrm_pfrag P) (l ++ (map wn (map dual lax))).
Proof with myeeasy.
intros P_perm P_axfree P_cut lax l ; intros pi.
apply cut_admissible_axfree...
apply deduction_list...
eapply stronger_pfrag...
nsplit 4...
simpl ; intros a.
exists (inr a)...
Qed.

Lemma deduction_inv {P} : pperm P = true -> (projT1 (pgax P) -> False) -> pcut P = true -> forall lax l,
  ll (cutrm_pfrag P) (l ++ (map wn (map dual lax))) ->
  ll (axupd_pfrag P (existT (fun x => x -> list formula) { k | k < length lax }
                            (fun a => nth (proj1_sig a) lax one :: nil))) l.
Proof with myeeasy.
intros P_perm P_axfree P_cut lax l ; intros pi.
assert (ll P (l ++ (map wn (map dual lax)))) as pi'.
{ eapply stronger_pfrag...
  nsplit 4...
  simpl ; intros a.
  exists a... }
apply deduction_list_inv in pi'...
eapply stronger_pfrag...
nsplit 4...
simpl ; intros a.
destruct a.
- contradiction P_axfree.
- exists s...
Qed.

