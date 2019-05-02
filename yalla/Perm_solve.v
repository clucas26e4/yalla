

Require Export all_lt_solve.
Require Export all_distinct_solve.
Require Export misc.
Require Import List_more.
Require Import Perm.
Require Import List_nat.
Require Import List_manip.

Ltac is_perm_run :=
  match goal with
  | |- is_perm _ = true => unfold is_perm; apply andb_true_intro; split; [ repeat all_lt_run | rewrite ? incr_all_plus; repeat all_distinct_solve ]
  end.

Ltac app_nat_fun_solve :=
  rewrite<- ? app_assoc;
  rewrite ? app_nat_fun_app;
  rewrite ? incr_all_plus;
  repeat (rewrite app_nat_fun_right ; [ | repeat all_lt_run]);
  repeat (rewrite app_nat_fun_left ; [ | repeat all_lt_run]);
  rewrite ? app_Id;
  reflexivity.

Fixpoint create_part_perm {A} (l : list (list A)) i :=
  match l, i with
  | nil, _ => nil
  | a :: l , 0 => Id (length a)
  | a :: l , S k => incr_all (create_part_perm l k) (length a)
  end.

Fixpoint create_perm {A} (l1 : list (list A)) l2 :=
  match l2 with
  | nil => nil
  | i :: nil => create_part_perm l1 i
  | i :: l => create_part_perm l1 i ++ create_perm l1 l
  end.

Ltac prove_perm l l1 l2 :=
  replace l with
    (app_nat_fun (concat l1) (create_perm l1 l2)) ; unfold concat at 1; unfold create_perm; unfold create_part_perm; [ | app_nat_fun_solve].