Require Import Compare.
Require Import Bool.
Require Import Sumbool.
Require Import Arith.
Require Import ZArith.
Require Import Allmaps.
Require Import List.

Section BDDmisc.

Definition BDDvar := ad.

Definition BDDcompare (x y : BDDvar) :=
  match x, y with
  | ad_z, ad_z => Datatypes.Eq
  | ad_z, ad_x _ => Datatypes.Lt
  | ad_x _, ad_z => Datatypes.Gt
  | ad_x p1, ad_x p2 => (p1 ?= p2)%positive Datatypes.Eq
  end.

Definition ad_S (a : ad) :=
  match a with
  | ad_z => ad_x 1
  | ad_x p => ad_x (Psucc p)
  end.

Definition max (m n : nat) := if nat_le m n then n else m.

Definition BDDvar_max (x y : BDDvar) := if ad_le x y then y else x.

Inductive no_dup_list (A : Set) : list A -> Prop :=
  | no_dup_nil : no_dup_list A nil
  | no_dup_cons :
      forall (a : A) (l : list A),
      ~ In a l -> no_dup_list _ l -> no_dup_list _ (a :: l).

Lemma ad_S_is_S : forall a : ad, nat_of_ad (ad_S a) = S (nat_of_ad a).
Proof.
  simple induction a. reflexivity.  simpl in |- *. unfold nat_of_P in |- *. intro.
  exact (Pmult_nat_succ_morphism p 1).
Qed.

Lemma relation_sum :
 forall r : Datatypes.comparison,
 {r = Datatypes.Eq} + {r = Datatypes.Lt} + {r = Datatypes.Gt}.
Proof.
  intro.  elim r.  left; left; reflexivity.  left; right; reflexivity.  right; reflexivity.
Qed.

Lemma BDD_EGAL_complete :
 forall x y : BDDvar, BDDcompare x y = Datatypes.Eq -> x = y.
Proof.
  double induction x y.  reflexivity.  simpl in |- *.  intros; discriminate.  simpl in |- *.
  intros; discriminate.  simpl in |- *.  intros.  cut (p0 = p).  intro.  rewrite H0; reflexivity.
  apply Pcompare_Eq_eq.  assumption.
Qed.

Lemma BDDcompare_lt :
 forall x y : BDDvar,
 BDDcompare x y = Datatypes.Lt -> nat_of_ad x < nat_of_ad y.
Proof.
  double induction x y.  simpl in |- *.  intro.  discriminate.  simpl in |- *.  intros.
  cut (exists h : nat, nat_of_P p = S h).  intro.  inversion H0.  rewrite H1.
  apply lt_O_Sn.  apply ZL4.  simpl in |- *.  intros.  discriminate.  simpl in |- *.  intros.
  apply nat_of_P_lt_Lt_compare_morphism.  assumption.
Qed.

Lemma BDDlt_compare :
 forall x y : BDDvar,
 nat_of_ad x < nat_of_ad y -> BDDcompare x y = Datatypes.Lt.
Proof.
  double induction x y.  simpl in |- *.  intro.  absurd (0 < 0).  apply lt_n_O.  assumption.
  simpl in |- *.  reflexivity.  simpl in |- *.  intro.  cut (exists h : nat, nat_of_P p = S h).  intro.
  inversion H.  rewrite H0.  intro.  absurd (S x0 < 0).  apply lt_n_O.
  assumption.  apply ZL4.  simpl in |- *.  intro.  intros.  apply nat_of_P_lt_Lt_compare_complement_morphism.
  assumption.
Qed.

Lemma BDDcompare_trans :
 forall x y z : BDDvar,
 BDDcompare x y = Datatypes.Lt ->
 BDDcompare y z = Datatypes.Lt -> BDDcompare x z = Datatypes.Lt.
Proof.
  double induction x y.  simpl in |- *.  intros.  discriminate H.  simpl in |- *.  intro.
  simple induction z.  intros.  discriminate H0.  trivial.  simpl in |- *.  intros.
  discriminate H.  intro.  intro.  simple induction z.  simpl in |- *.  trivial.  intro.
  simpl in |- *.  intros.  cut (nat_of_P p0 < nat_of_P p).
  cut (nat_of_P p < nat_of_P p1).  intros.  apply nat_of_P_lt_Lt_compare_complement_morphism.
  apply lt_trans with (m := nat_of_P p).  assumption.  assumption.
  apply nat_of_P_lt_Lt_compare_morphism.  assumption.  apply nat_of_P_lt_Lt_compare_morphism.
  assumption.
Qed. 

Lemma BDDcompare_sup_inf :
 forall x y : BDDvar,
 BDDcompare x y = Datatypes.Gt -> BDDcompare y x = Datatypes.Lt.
Proof.
  double induction x y.  simpl in |- *.  intro; discriminate.  simpl in |- *.  intro.  intro; discriminate.
  simpl in |- *.  reflexivity.  unfold BDDcompare in |- *.  intros.  apply ZC1.  assumption.
Qed.

Lemma lt_trans_1 : forall x y z : nat, x < y -> y < S z -> x < z.
Proof.
  intros.  unfold lt in H0.  unfold lt in H.  unfold lt in |- *.
  apply le_trans with (m := y).  assumption.  apply le_S_n.  assumption.
Qed.

Lemma BDDcompare_1 :
 forall x y : BDDvar,
 BDDcompare x y = Datatypes.Lt ->
 BDDcompare (ad_S x) y = Datatypes.Lt \/ ad_S x = y.
Proof.
  intros.  elim (relation_sum (BDDcompare (ad_S x) y)).  intro H0.  elim H0; intro.
  right.  apply BDD_EGAL_complete.  assumption.  left; assumption.  intro.
  absurd (nat_of_ad x < nat_of_ad x).  apply lt_irrefl.  apply lt_trans_1 with (y := nat_of_ad y).
  apply BDDcompare_lt.  assumption.  rewrite <- (ad_S_is_S x).  apply BDDcompare_lt.
  apply BDDcompare_sup_inf.  assumption.
Qed.

Lemma andb3_lemma :
 forall b1 b2 b3 : bool,
 b1 && (b2 && b3) = true -> b1 = true /\ b2 = true /\ b3 = true.
Proof.
  intros b1 b2 b3.  elim b1.  simpl in |- *.  elim b2.  simpl in |- *.  auto.  simpl in |- *.
  intro; discriminate H.  simpl in |- *.  intro; discriminate H.
Qed.

Lemma andb3_lemma_1 :
 forall x x0 y y0 z z0 : ad,
 (x, (y, z)) <> (x0, (y0, z0)) ->
 ad_eq x x0 && (ad_eq y y0 && ad_eq z z0) = false.
Proof.
  intros x x0 y y0 z z0 H.  elim (sumbool_of_bool (ad_eq x x0)).  intro H0.
  elim (sumbool_of_bool (ad_eq y y0)).  intro H1.  elim (sumbool_of_bool (ad_eq z z0)).
  intro H2.  absurd ((x, (y, z)) = (x0, (y0, z0))).  assumption.  rewrite (ad_eq_complete _ _ H0).
  rewrite (ad_eq_complete _ _ H1).  rewrite (ad_eq_complete _ _ H2).  reflexivity.
  intro H2.  rewrite H0.  rewrite H1.  rewrite H2.  reflexivity.  intro H1.  rewrite H0.
  rewrite H1.  reflexivity.  intro H0.  rewrite H0.  reflexivity.  
Qed.

Lemma ad_S_le_then_neq :
 forall x y : ad, ad_le (ad_S x) y = true -> ad_eq x y = false.
Proof.
  intros.  cut (ad_eq x y = true \/ ad_eq x y = false).  intro.  elim H0.
  clear H0.  intro.  cut (x = y).  intro.  rewrite H1 in H.  unfold ad_le in H.
  rewrite (ad_S_is_S y) in H.
  cut (nat_le (S (nat_of_ad y)) (nat_of_ad y) = false).  rewrite H.  intro.
  discriminate H2.  cut (nat_of_ad y < S (nat_of_ad y)).  intro.
  apply nat_le_correct_conv.  assumption.  unfold lt in |- *.  trivial.
  apply ad_eq_complete.  assumption.  trivial. elim (ad_eq x y). auto. auto.
Qed.

Lemma BDD_EGAL_correct : forall x : BDDvar, BDDcompare x x = Datatypes.Eq.
Proof.
  simple induction x.  reflexivity.  simpl in |- *.  intros.  apply Pcompare_refl.
Qed.

Lemma BDDcompare_inf_sup :
 forall x y : BDDvar,
 BDDcompare x y = Datatypes.Lt -> BDDcompare y x = Datatypes.Gt.
Proof.
  double induction x y.  simpl in |- *.  intro; discriminate.  simpl in |- *.
  intro; reflexivity.  simpl in |- *.  intros; discriminate.  simpl in |- *.  intros.
  apply ZC2.  assumption.
Qed.

Lemma ad_S_compare :
 forall x y : ad, BDDcompare x y = BDDcompare (ad_S x) (ad_S y).
Proof.
  intros x y.  elim (relation_sum (BDDcompare x y)).  intro y0.  elim y0; clear y0; intro y0.
  rewrite (BDD_EGAL_complete x y y0).  rewrite (BDD_EGAL_correct y).
  rewrite (BDD_EGAL_correct (ad_S y)).  reflexivity.  rewrite y0.  symmetry  in |- *.
  apply BDDlt_compare.  rewrite (ad_S_is_S x).  rewrite (ad_S_is_S y).
  apply lt_n_S.  apply BDDcompare_lt.  assumption.  intro y0.  simpl in |- *.  simpl in |- *.
  simpl in |- *.  rewrite y0.  symmetry  in |- *.  apply BDDcompare_inf_sup.  apply BDDlt_compare.
  rewrite (ad_S_is_S x).  rewrite (ad_S_is_S y).  apply lt_n_S.  apply BDDcompare_lt.
  apply BDDcompare_sup_inf.  assumption.
Qed.

Lemma prod_sum :
 forall (A B : Set) (p : A * B), exists a : A, (exists b : B, p = (a, b)).
Proof.
  intros A B p.  elim p.  intros y y0.  split with y.  split with y0.  reflexivity.
Qed.

Lemma lt_max_1_2 :
 forall x1 y1 x2 y2 : nat, x1 < x2 -> y1 < y2 -> max x1 y1 < max x2 y2.
Proof.
  intros x1 y1 x2 y2 H H0.  unfold max in |- *.  elim (sumbool_of_bool (nat_le x2 y2)). 
  intro y.  rewrite y.
  elim (nat_le x1 y1).  assumption.  apply lt_le_trans with (m := x2).  assumption.
  apply nat_le_complete.  assumption.  intro y.  rewrite y.  elim (nat_le x1 y1).
  apply lt_trans with (m := y2).  assumption.  apply nat_le_complete_conv.  assumption.
  assumption.
Qed.

Lemma lt_max_1 :
 forall x1 y1 x2 y2 : nat, x1 < x2 -> y1 < x2 -> max x1 y1 < max x2 y2.
Proof.
  intros x1 y1 x2 y2 H H0.  unfold max in |- *.  elim (nat_le x1 y1).
  elim (sumbool_of_bool (nat_le x2 y2)); intro y; rewrite y.
  apply lt_le_trans with (m := x2).  assumption.  apply nat_le_complete; assumption.
  assumption.  elim (sumbool_of_bool (nat_le x2 y2)).  intro y.  rewrite y.  apply lt_le_trans with (m := x2).
  assumption.  apply nat_le_complete; assumption.  intro y; rewrite y.  assumption.
Qed.

Lemma lt_max_2 :
 forall x1 y1 x2 y2 : nat, x1 < y2 -> y1 < y2 -> max x1 y1 < max x2 y2.
Proof.
  intros x1 y1 x2 y2 H H0.  unfold max in |- *.  elim (nat_le x1 y1).  elim (sumbool_of_bool (nat_le x2 y2)).
  intro y.  rewrite y.  assumption.  intro y.  rewrite y.  apply lt_trans with (m := y2).
  assumption.  apply nat_le_complete_conv.  assumption.  elim (sumbool_of_bool (nat_le x2 y2)).
  intro y.  rewrite y.  assumption.  intro y.  rewrite y.  apply lt_trans with (m := y2).
  assumption.  apply nat_le_complete_conv.  assumption.
Qed.

Lemma max_x_x_eq_x : forall x : nat, max x x = x.
Proof.
  unfold max in |- *.  intro.  elim (nat_le x x).  reflexivity.  reflexivity.
Qed.

Lemma BDDvar_le_max_2 : forall x y : BDDvar, ad_le x (BDDvar_max y x) = true.
Proof.
  unfold BDDvar_max in |- *.  intros x y.  elim (sumbool_of_bool (ad_le y x)).
  intro y0.  rewrite y0.  apply ad_le_refl.  intro y0.  rewrite y0.
  apply ad_lt_le_weak.  assumption.
Qed.

Lemma BDDvar_max_max :
 forall x y : BDDvar,
 nat_of_ad (BDDvar_max x y) = max (nat_of_ad x) (nat_of_ad y).
Proof.
  unfold BDDvar_max, max in |- *.  intros.  unfold ad_le in |- *.
  elim (nat_le (nat_of_ad x) (nat_of_ad y)).  reflexivity.  reflexivity.
Qed.

Lemma BDDvar_le_max_1 : forall x y : BDDvar, ad_le x (BDDvar_max x y) = true.
Proof.
  intros x y.  elim (sumbool_of_bool (ad_le x y)); unfold BDDvar_max in |- *.
  intro y0.  rewrite y0.  assumption.  intro y0.  rewrite y0.  apply ad_le_refl.
Qed.

Lemma BDDvar_max_inf :
 forall x y : BDDvar, BDDcompare x y = Datatypes.Lt -> BDDvar_max x y = y.
Proof.
  intros.  unfold BDDvar_max in |- *.  replace (ad_le x y) with true.  reflexivity.
  symmetry  in |- *.  unfold ad_le in |- *.  apply nat_le_correct.  apply lt_le_weak.
  apply BDDcompare_lt.  assumption.
Qed.

Lemma BDDvar_max_comm : forall x y : BDDvar, BDDvar_max x y = BDDvar_max y x.
Proof.
  unfold BDDvar_max in |- *.  intros x y.  elim (sumbool_of_bool (ad_le x y)).
  intro y0.  rewrite y0.  elim (sumbool_of_bool (ad_le y x)).  intro y1.  rewrite y1.
  apply ad_le_antisym.  assumption.  assumption.  intro y1.  rewrite y1.
  reflexivity.  intro y0.  rewrite y0.  elim (sumbool_of_bool (ad_le y x)).  intro y1.
  rewrite y1.  reflexivity.  intro y1.  rewrite y1.  apply ad_le_antisym.
  apply ad_lt_le_weak.  assumption.  apply ad_lt_le_weak.  assumption.
Qed.

Lemma nat_gt_1_lemma : forall n : nat, n <> 0 -> n <> 1 -> 2 <= n.
Proof.
  intros.  cut (1 <= n).  intro.  elim (le_le_S_eq _ _ H1).  tauto.  intro.
  absurd (n = 1).  assumption.  symmetry  in |- *.  assumption.  fold (0 < n) in |- *.
  apply neq_O_lt.  unfold not in |- *.  intro.  apply H.  rewrite H1; reflexivity.  
Qed.

Lemma ad_gt_1_lemma :
 forall x : ad, x <> ad_z -> x <> ad_x 1 -> ad_le (ad_x 2) x = true.
Proof.
  intros.  unfold ad_le in |- *.  unfold nat_of_ad at 1 in |- *.  unfold nat_of_P in |- *.
  unfold Pmult_nat in |- *.  unfold plus in |- *.  apply nat_le_correct.
  apply nat_gt_1_lemma.  unfold not in |- *.  intro.  apply H.
  replace ad_z with (ad_of_nat 0).  rewrite <- H1.  symmetry  in |- *.
  apply ad_of_nat_of_ad.  reflexivity.  unfold not in |- *.  intro.  apply H0.
  replace (ad_x 1) with (ad_of_nat 1).  rewrite <- H1.  symmetry  in |- *.
  apply ad_of_nat_of_ad.  reflexivity.  
Qed.

Lemma ad_lt_lemma :
 forall a b : ad, ad_le a b = false -> ad_le (ad_S b) a = true.
Proof.
  intros.  unfold ad_le in |- *.  rewrite (ad_S_is_S b).  apply nat_le_correct.
  fold (nat_of_ad b < nat_of_ad a) in |- *.  apply nat_le_complete_conv.
  assumption.
Qed.

Lemma eq_ad_S_eq :
 forall a b : ad, ad_eq (ad_S a) (ad_S b) = true -> ad_eq a b = true.
Proof.
  intros.  cut (ad_S a = ad_S b).  rewrite <- (ad_of_nat_of_ad (ad_S a)).
  rewrite <- (ad_of_nat_of_ad (ad_S b)).  rewrite (ad_S_is_S a).
  rewrite (ad_S_is_S b).  intro.  cut (nat_of_ad a = nat_of_ad b).  intro.
  rewrite <- (ad_of_nat_of_ad a).  rewrite <- (ad_of_nat_of_ad b).  rewrite H1.
  apply ad_eq_correct.  apply eq_add_S.
  rewrite <- (nat_of_ad_of_nat (S (nat_of_ad a))).  rewrite H0.
  apply nat_of_ad_of_nat.  apply ad_eq_complete.  assumption.
Qed.

Lemma ad_S_neq_ad_z : forall a : ad, ad_eq (ad_S a) ad_z = false.
Proof.
  intros.  elim a.  reflexivity.  simpl in |- *.  reflexivity.
Qed.

Lemma list_sum :
 forall (A : Set) (l : list A),
 l = nil \/ (exists a : A, (exists l' : list A, l = a :: l')).
Proof.
  intros.  elim l.  left; reflexivity.  intros.  right.  split with a.
  split with l0.  reflexivity.
Qed. 

Lemma no_dup_sum :
 forall (A : Set) (l : list A) (H : no_dup_list _ l),
 l = nil \/
 (exists a : A,
    (exists l0 : list A, ~ In a l0 /\ no_dup_list _ l0 /\ l = a :: l0)).
Proof.
  intros.  elim H.  left; reflexivity.  intros.  right.  split with a.
  split with l0.  split.  assumption.  split.  assumption.  reflexivity.
Qed.

Lemma no_dup_cons_no_dup :
 forall (A : Set) (l : list A) (a : A),
 no_dup_list _ (a :: l) -> no_dup_list _ l.
Proof.
  intros.  elim (no_dup_sum _ _ H).  intro; discriminate.  intros.
  elim H0; intros.  elim H1; intros.  elim H2; intros.  elim H4; intros.
  injection H6.  intros.  rewrite H7; assumption.
Qed.

Lemma no_dup_cons_no_in :
 forall (A : Set) (l : list A) (a : A), no_dup_list _ (a :: l) -> ~ In a l.
Proof.
  intros.  elim (no_dup_sum _ _ H).  intro; discriminate.  intros.
  elim H0; intros.  elim H1; intros.  elim H2; intros.  elim H4; intros.
  injection H6.  intros.  rewrite H7; rewrite H8; assumption.
Qed.

End BDDmisc.