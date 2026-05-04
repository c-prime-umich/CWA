Require Import VST.floyd.functional_base.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require spec_math.

(** We [Require] the [mathcomp] files, but without [Import] because we don't want
   to use [ssreflect] tactics in VST proofs, and we don't want the namespace polluted with
   all that mathcomp stuff.
*) 
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype finfun bigop finset fingroup perm order.
From mathcomp Require Import div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
(** Among all the mathcomp stuff, these are the files that we *do* want to Import: *)
Import fintype matrix.

Require LAProof.accuracy_proofs.export.
Module F := LAProof.accuracy_proofs.mv_mathcomp.F.

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


Definition never_nan:   sig (fun x : float => eq (Binary.is_nan (fprec Tdouble) (femax Tdouble) x) true)
 := FPCore.any_nan (fprec Tdouble) (femax Tdouble) (fprec_lt_femax Tdouble).

Definition BFLOOR (x : Binary.binary_float (fprec Tdouble) (femax Tdouble)) : Binary.binary_float (fprec Tdouble) (femax Tdouble)
 (* remark: if x is finite, then Bnearbyint is never a nan, so never_nan will never be used *)
  := if Binary.is_finite x 
   then Binary.BSN2B _ _ never_nan
  (@BinarySingleNaN.Bnearbyint (fprec Tdouble) (femax Tdouble) (fprec_lt_femax Tdouble)  BinarySingleNaN.mode_DN 
   (Binary.B2BSN _ _ x))
  else x.

Lemma BCMP_eq: forall op b [t: type] (x y: ftype t),
    Binary.is_finite x = true ->
    Binary.is_finite y = true ->
   BCMP op b x y =
    match op, b with
     | Gt, false => Rle_bool (Binary.B2R _ _ x) (Binary.B2R _ _ y)
     | Gt, true => Rlt_bool (Binary.B2R _ _ y) (Binary.B2R _ _ x)
     | Lt, false => Rle_bool (Binary.B2R _ _ y) (Binary.B2R _ _ x)
     | Lt, true => Rlt_bool (Binary.B2R _ _ x) (Binary.B2R _ _ y)
     | Eq, true => Req_bool (Binary.B2R _ _ x) (Binary.B2R _ _ y)
     | Eq, false => negb (Req_bool (Binary.B2R _ _ x) (Binary.B2R _ _ y))
    end.
Proof.
intros.
unfold BCMP, extend_comp.
rewrite Binary.Bcompare_correct; auto.
forget (Binary.B2R _ _ x) as x'. forget (Binary.B2R _ _ y) as y'.
clear.
destruct op, b; auto; destruct (Rcompare x' y') eqn:?H.
- rewrite (Rcompare_Eq_inv _ _ H) Req_bool_true //.
- apply Rcompare_Lt_inv in H; rewrite Req_bool_false; auto; Lra.lra.
- apply Rcompare_Gt_inv in H; rewrite Req_bool_false; auto; Lra.lra.
- rewrite (Rcompare_Eq_inv _ _ H) Rle_bool_true //. Lra.lra.
- apply Rcompare_Lt_inv in H; rewrite Rle_bool_false; auto; Lra.lra.
- apply Rcompare_Gt_inv in H; rewrite Rle_bool_true; auto; Lra.lra.
- rewrite (Rcompare_Eq_inv _ _ H) Rlt_bool_false //. Lra.lra.
- apply Rcompare_Lt_inv in H; rewrite Rlt_bool_false; auto; Lra.lra.
- apply Rcompare_Gt_inv in H; rewrite Rlt_bool_true; auto; Lra.lra.
Qed.

Lemma BCMP_Rle_bool:
 forall [t: type] (x y: ftype t),
    Binary.is_finite x = true ->
    Binary.is_finite y = true ->
    BCMP Gt false x y = Rle_bool (Binary.B2R (fprec t) (femax t) x) (Binary.B2R (fprec t) (femax t) y).
Proof.
intros.
rewrite BCMP_eq; auto.
Qed.


Lemma BCMP_Rlt_bool:
 forall [t: type] (x y: ftype t),
    Binary.is_finite x = true ->
    Binary.is_finite y = true ->
    BCMP Gt true x y = Rlt_bool (Binary.B2R (fprec t) (femax t) y) (Binary.B2R (fprec t) (femax t) x).
Proof.
intros.
rewrite BCMP_eq; auto.
Qed.

Lemma Btrunc_range_pos: forall (hi: Z) (x: ftype Tdouble),
  (0 <= hi < Int.max_signed)%Z ->
  (Zconst Tdouble 0 <= x <= Zconst Tdouble hi)%F64 ->
  Binary.is_finite x = true ->
  (0 <= Binary.Btrunc _ _ x <= hi)%Z.
Proof.
intros.
assert (Rdefinitions.Rle (Rdefinitions.IZR 0) (Rdefinitions.IZR (Binary.Btrunc (fprec Tdouble) (femax Tdouble) x))
            /\  Rdefinitions.Rle (Rdefinitions.IZR (Binary.Btrunc (fprec Tdouble) (femax Tdouble) x)) (Rdefinitions.IZR hi)).
2: destruct H2; split; apply RIneq.le_IZR; auto.
destruct H0.
erewrite Binary.Btrunc_correct by reflexivity.
rewrite FIX.round_FIX_IZR.
unfold Zconst in *.
rewrite (proof_irr (Pos2Z.is_pos (fprecp Tdouble)) (fprec_lt_femax Tdouble)) in H0,H2.
decompose [and] (BofZ_exact _ _ (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble) 0 ltac:(simpl; unfold Z.pow_pos; simpl; clear - H H0; rep_lia)) .
decompose [and] (BofZ_exact _ _ (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble) hi ltac:(simpl; unfold Z.pow_pos; simpl; clear - H H0; rep_lia)).
rewrite BCMP_Rle_bool in H0; auto.
rewrite BCMP_Rle_bool in H2; auto.
rewrite H4 in H2.
rewrite H3 in H0.
destruct (Rle_bool_spec (Binary.B2R (fprec Tdouble) (femax Tdouble) x) (Rdefinitions.IZR hi)); try discriminate.
destruct (Rle_bool_spec (Rdefinitions.IZR 0) (Binary.B2R (fprec Tdouble) (femax Tdouble) x)); try discriminate.
forget (Binary.B2R _ _ x) as y.
apply Ztrunc_le in H10.
rewrite Ztrunc_IZR in H10.
apply RIneq.IZR_le in H10.
apply Ztrunc_le in H7.
rewrite Ztrunc_IZR in H7.
apply RIneq.IZR_le in H7.
auto.
Qed.

Section RDEF.
Import Rdefinitions.

Lemma round_between_nats: forall x n,
   Z.of_nat n <= Int.max_signed ->
  (0 <= x <= IZR (Z.of_nat n))%R ->
  (0 <= Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec Tdouble) (femax Tdouble)) (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) x <= IZR (Z.of_nat n))%R.
Proof.
intros.
pose proof Generic_fmt.round_le Zaux.radix2 (SpecFloat.fexp (fprec Tdouble) (femax Tdouble)) (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) .
pose proof (H1 x (IZR (Z.of_nat n)) ltac:(Lra.lra)).
specialize (H1 0%R x ltac:(Lra.lra)).
rewrite Generic_fmt.round_0 in H1.
split; auto.
clear H1.
pose proof  (BofZ_correct (fprec Tdouble) (femax Tdouble) (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble) (Z.of_nat n)).
rewrite Rlt_bool_true in H1.
destruct H1 as [? _].
rewrite <- H1 in H2.
-
destruct (BofZ_exact (fprec Tdouble) (femax Tdouble) (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble) (Z.of_nat n)
  ltac:(simpl; unfold Z.pow_pos; simpl; rep_lia)) as [? _].
Lra.lra.
-
clear H0 H2 x.
rewrite Generic_fmt.round_generic.
rewrite Rbasic_fun.Rabs_pos_eq.
simpl. apply RIneq.IZR_lt. rep_lia.
apply RIneq.IZR_le. lia.
apply (Lang_expr.generic_format_fexp_IZR (Z.of_nat n) (fprec Tdouble) (femax Tdouble)); try apply erefl.
simpl; rep_lia.
Qed.

Lemma Rabs_round_range: forall x n,
   Z.of_nat n <= Int.max_signed ->
  (0 <= x <= IZR (Z.of_nat n))%R ->
  (Rbasic_fun.Rabs (Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec Tdouble) (femax Tdouble)) (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) x) <
  bpow Zaux.radix2 (femax Tdouble))%R.
Proof.
intros.
pose proof (round_between_nats x n H H0).
set (x' := Generic_fmt.round _ _ _ x) in H1|-*. clearbody x'.
clear x H0.
simpl bpow.
destruct H1.
rewrite Rbasic_fun.Rabs_pos_eq; auto.
eapply RIneq.Rle_lt_trans. apply H1.
apply RIneq.IZR_lt.
rep_lia.
Qed.

End RDEF.

Lemma Fle_Zconst: forall [t] (i j: Z), 
   (   - 2 ^ (fprec t)  <= i <= j)%Z -> 
    (j <= 2 ^ (fprec t)) -> 
 is_true (BCMP Gt false (Zconst t i) (Zconst t j)).
Proof.
intros.
destruct (BofZ_exact  (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) i ltac:(lia)) as [? [? _]].
destruct (BofZ_exact  (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) j ltac:(lia)) as [? [? _]].
unfold Zconst; rewrite (proof_irr (Pos2Z.is_pos (fprecp t)) (fprec_gt_0 t)).
rewrite BCMP_eq; auto.
rewrite H1 H3.
apply Rle_bool_true.
apply RIneq.IZR_le.
destruct H; auto.
Qed.

Lemma BFLOOR_le: forall (x: ftype Tdouble), 
       is_true (Binary.is_finite x) -> is_true (BCMP Gt false (BFLOOR x) x).
Proof.
intros.
unfold BFLOOR.
rewrite H.
pose proof BinarySingleNaN.Bnearbyint_correct _ _ (fprec_lt_femax Tdouble) BinarySingleNaN.mode_DN
   (Binary.B2BSN (fprec Tdouble) (femax Tdouble) x).
destruct H0 as [? [? _]].
assert (BinarySingleNaN.is_finite (Binary.B2BSN (fprec Tdouble) (femax Tdouble) x) = true).
destruct x; try discriminate; auto.
rewrite H2 in H1.
set u := BinarySingleNaN.Bnearbyint _ _ in H0,H1|-*. clearbody u.
rewrite FIX.round_FIX_IZR in H0.
unfold BCMP.
unfold extend_comp.
unfold Binary.Bcompare.
rewrite Binary.B2BSN_BSN2B.
rewrite BinarySingleNaN.Bcompare_correct; auto.
rewrite Binary.B2R_B2BSN.
rewrite H0.
rewrite Binary.B2R_B2BSN.
unfold BinarySingleNaN.round_mode.
destruct (Rcompare _ _) eqn:?H; auto.
pose proof Zfloor_lb (Binary.B2R _ _ x).
apply Rcompare_not_Gt in H4.
congruence.
Qed.

Lemma BFLOOR_le': forall (i: Z) (x: ftype Tdouble), 
    is_true (Binary.is_finite x) ->
    - 2 ^ fprec Tdouble <= i <= 2 ^ fprec Tdouble ->
    is_true (Zconst Tdouble i <= x)%F64 ->
   is_true (Zconst Tdouble i <= BFLOOR x)%F64.
Proof.
intros * H REPi Hi.
assert (FINi: is_true (Binary.is_finite (Zconst Tdouble i))) by (apply BofZ_exact; auto).
unfold BFLOOR.
rewrite H.
unfold BCMP.
unfold extend_comp.
unfold Binary.Bcompare.
pose proof BinarySingleNaN.Bnearbyint_correct _ _ (fprec_lt_femax Tdouble) BinarySingleNaN.mode_DN
   (Binary.B2BSN (fprec Tdouble) (femax Tdouble) x).
destruct H0 as [? [? ?]].
assert (BinarySingleNaN.is_finite (Binary.B2BSN (fprec Tdouble) (femax Tdouble) x) = true).
destruct x; try discriminate; auto.
rewrite H3 in H1.
spec H2.
destruct (BinarySingleNaN.Bnearbyint BinarySingleNaN.mode_DN _); auto.
rewrite Binary.B2BSN_BSN2B.
rewrite BinarySingleNaN.Bcompare_correct; auto.
2: destruct (Zconst Tdouble i); try discriminate; simpl; auto.
rewrite Binary.B2R_B2BSN.
rewrite H0.
rewrite FIX.round_FIX_IZR.
rewrite Binary.B2R_B2BSN.
unfold BinarySingleNaN.round_mode.
assert (Rdefinitions.Rle (Binary.B2R (fprec Tdouble) (femax Tdouble) (Zconst Tdouble i))
      (Rdefinitions.IZR (Zfloor (Binary.B2R (fprec Tdouble) (femax Tdouble) x)))).
2: apply Rcompare_not_Gt in H4; destruct (Rcompare _ _); try congruence.
assert (Rdefinitions.Rle (Binary.B2R (fprec Tdouble) (femax Tdouble) (Zconst Tdouble i))
        (Binary.B2R (fprec Tdouble) (femax Tdouble) x)). {
  unfold BCMP in Hi.
  unfold extend_comp in Hi.
  rewrite Binary.Bcompare_correct in Hi; auto.
  apply Rcompare_not_Gt_inv.
  destruct (Rcompare _ _); auto; try discriminate.
}
clear Hi.
unfold Zconst in *.
destruct (BofZ_exact _ _ (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble) i REPi) as [? _].
rewrite (proof_irr (Pos2Z.is_pos (fprecp Tdouble) )(fprec_gt_0 Tdouble)) in H4|-*.
rewrite H5 in H4|-*.
pose proof Zfloor_lub _ _ H4.
apply RIneq.IZR_le; auto.
Qed.

Lemma BFLOOR_finite: forall x, is_true (Binary.is_finite x) -> is_true (Binary.is_finite (BFLOOR x)).
Proof.
intros.
unfold BFLOOR.
rewrite H.
rewrite Binary.is_finite_BSN2B.
decompose [and] ( BinarySingleNaN.Bnearbyint_correct _ _ (fprec_lt_femax Tdouble)
     BinarySingleNaN.mode_DN
        (Binary.B2BSN (fprec Tdouble) (femax Tdouble) x)).
rewrite H2.
rewrite Binary.is_finite_B2BSN.
auto.
Qed.

Definition Bexp : ftype Tdouble -> ftype Tdouble := FPCore.ff_func VSTlib.spec_math.MF.exp.

Lemma forallb_rev: forall {A} (f: A -> bool) (al: list A), forallb f (rev al) = forallb f al.
induction al.
reflexivity.
change (cons a al) with ([::a]++al).
rewrite rev_cat.
simpl.
rewrite forallb_app IHal.
simpl.
destruct (forallb f al), (f a); tauto.
Qed.

Lemma Fle_trans: forall [t] (x y z: ftype t),
     is_true (BCMP Gt false x y) -> 
     is_true (BCMP Gt false y z) -> 
     is_true (BCMP Gt false x z).
Proof.
intros.
unfold BCMP in *.
destruct x; try destruct s; try discriminate;
destruct y; try destruct s; try discriminate;
destruct z; try destruct s; try discriminate; auto;
unfold extend_comp in *;
unfold Binary.Bcompare,BinarySingleNaN.Bcompare, BinarySingleNaN.B2SF, Binary.B2BSN, SpecFloat.SFcompare in *;
unfold CompOpp in *;
destruct (e ?= e3) eqn:?H; auto;
try apply Z.compare_eq in H1; subst.
-
destruct (e3?= e1) eqn:H2; auto;
try apply Z.compare_eq in H2; subst.
+
rewrite Z.compare_refl in H0.
destruct (PosDef.Pos.compare_cont Eq m m1) eqn:H1; auto.
apply nat_of_P_lt_Lt_compare_morphism in H1.
destruct (PosDef.Pos.compare_cont Eq m m0) eqn:H2.
*
apply Pcompare_Eq_eq in H2; subst.
rewrite nat_of_P_lt_Lt_compare_complement_morphism in H0; auto.
*
apply nat_of_P_lt_Lt_compare_morphism in H2; auto.
*
apply nat_of_P_gt_Gt_compare_morphism in H2.
destruct (PosDef.Pos.compare_cont Eq m0 m1) eqn:H3; try discriminate.
apply Pcompare_Eq_eq in H3; subst; lia.
apply nat_of_P_gt_Gt_compare_morphism in H3.
lia.
+
destruct (PosDef.Pos.compare_cont Eq m m1) eqn:H3; try discriminate; auto.
apply nat_of_P_lt_Lt_compare_morphism in H3.
destruct (IntDef.Z.compare e1 e3) eqn:?H; try discriminate.
try apply Z.compare_eq in H1; subst.
rewrite Z.compare_refl in H2; discriminate.
rewrite Z.compare_gt_iff in H2.
rewrite Z.compare_gt_iff in H1. lia.
-
destruct (IntDef.Z.compare e1 e3) eqn:?H; try discriminate.
apply Z.compare_eq in H2; subst.
destruct (IntDef.Z.compare e e3) eqn:?H; try discriminate.
destruct (IntDef.Z.compare e e1) eqn:?H; try discriminate.
apply Z.compare_eq in H3; subst.
congruence.
pose proof Zcompare_Gt_trans _ _ _ H3 H2.
congruence.
-
destruct (IntDef.Z.compare e1 e3) eqn:?H; try discriminate.
apply Z.compare_eq in H1; subst.
rewrite Z.compare_refl in H.
destruct (PosDef.Pos.compare_cont Eq m m1) eqn:H3; try discriminate; auto.
destruct (PosDef.Pos.compare_cont Eq m m0) eqn:H4; try discriminate; auto.
apply Pcompare_Eq_eq in H4; subst.
rewrite H3 in H0. discriminate.
destruct (PosDef.Pos.compare_cont Eq m0 m1) eqn:H5; try discriminate; auto.
apply Pcompare_Eq_eq in H5; subst.
congruence.
apply nat_of_P_lt_Lt_compare_morphism in H5,H4.
apply nat_of_P_gt_Gt_compare_morphism in H3.
lia.
destruct (IntDef.Z.compare e3 e1) eqn:?H; try discriminate.
apply Z.compare_eq in H2; subst.
rewrite Z.compare_refl in H1; discriminate.
pose proof Zcompare_Lt_trans _ _ _ H1 H2.
rewrite Z.compare_refl in H3. inv H3.
-
destruct (IntDef.Z.compare e1 e3) eqn:?H; try discriminate.
apply Z.compare_eq in H2; subst.
rewrite H1 in H.
destruct (PosDef.Pos.compare_cont Eq m0 m1) eqn:H5; try discriminate; auto.
destruct (IntDef.Z.compare e e1) eqn:?H; try discriminate.
apply Z.compare_eq in H3; subst.
congruence.
pose proof Zcompare_Lt_trans _ _ _ H3 H2.
congruence.
Qed.

Section RDEF.
Import Rdefinitions.

Lemma interpolate_range: forall [Nfr Nbg: nat]
    (H0: 1 < Z.of_nat (S Nfr) <= Int.max_signed)
    (H1: Z.of_nat (S Nbg) <= Int.max_signed)
   (k: 'I_Nfr.+1),
  let j := BMULT (BDIV (Zconst Tdouble (Z.of_nat k)) (Zconst Tdouble (Z.of_nat Nfr))) (Zconst Tdouble (Z.of_nat Nbg)) in
  Binary.is_finite j = true /\   (0 <= j <= Zconst Tdouble (Z.of_nat Nbg))%F64.
Proof.
intros * [H2 ?] ? ?.
unfold Zconst.
rewrite (proof_irr (Pos2Z.is_pos (fprecp Tdouble)) (fprec_lt_femax Tdouble)).
unfold BMULT, BDIV, BINOP.
set (nan := FPCore.div_nan _ _ _); clearbody nan.
set (nan' := FPCore.mult_nan _ _ _); clearbody nan'.
set (k' := BofZ _ _ _ _ (Z.of_nat k)).
set (Nfr' := BofZ _ _ _ _ (Z.of_nat Nfr)).
set (Nbg' := BofZ _ _ _ _ _).
set (prec := fprec Tdouble) in *.
set (emax := femax Tdouble) in *.
set (F1 := fprec_gt_0 Tdouble) in *.
set (F2 := fprec_lt_femax Tdouble) in *.
destruct (BofZ_exact prec emax F1 F2 (Z.of_nat Nfr)) as [EQfr [FINfr SIGNfr]];
  [ simpl; unfold Z.pow_pos; simpl; rep_lia | ].
destruct (BofZ_exact prec emax F1 F2 (Z.of_nat k)) as [EQk [FINk SIGNk]];
  [pose proof ltn_ord k; simpl; unfold Z.pow_pos; simpl; rep_lia | ].
destruct (BofZ_exact prec emax F1 F2 (Z.of_nat Nbg)) as [EQbg [FINbg SIGNbg]];
  [simpl; unfold Z.pow_pos; simpl; rep_lia | ].
change (BofZ _ _ _ _ (Z.of_nat k)) with k' in EQk, FINk, SIGNk.
change (BofZ _ _ _ _ (Z.of_nat Nfr)) with Nfr' in EQfr, FINfr, SIGNfr.
change (BofZ _ _ _ _ (Z.of_nat Nbg)) with Nbg' in EQbg, FINbg, SIGNbg.
set (y := Binary.Bmult _ _ _ _ _ _ _ _).
assert (Binary.is_finite y = true /\ (0 <= Binary.B2R _ _ y <=Binary.B2R _ _ Nbg')%R).
2: destruct H0 as [? [? ?]]; split3; auto; rewrite BCMP_Rle_bool; auto; apply Rle_bool_true; auto.
rewrite EQbg.
pose proof Binary.Bdiv_correct prec emax F1 F2 nan BinarySingleNaN.mode_NE k' Nfr'.
spec H0; [ clear H0 y; rewrite EQfr; intro Hx; apply RIneq.eq_IZR in Hx; lia | ].
rewrite EQk EQfr in H0.
set (d := Rdiv _ _) in H0.
assert (Hd: (0 <= d <= 1)%R). {
 clear - H2. subst d. pose proof ltn_ord k.
 split.
 apply Stdlib.Rdiv_pos_compat.
 apply RIneq.IZR_le. lia.
 apply RIneq.IZR_lt. lia.
 apply Generic_proof.Rdiv_ge_mult_pos. apply RIneq.IZR_lt; lia.
 rewrite RIneq.Rmult_1_r.
 apply RIneq.IZR_le. lia.
}
rewrite Rlt_bool_true in H0.
2:{ apply (Rabs_round_range d 1). clear; rep_lia. apply Hd. }
assert (H3: (0 <= Generic_fmt.round Zaux.radix2 (SpecFloat.fexp prec emax) (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) d <= 1)%R). {
 clearbody d; clear - Hd.
 change 1%R with (IZR (Z.of_nat 1)).
 apply round_between_nats; auto. clear; rep_lia. 
}
destruct H0 as [EQd [FINd SIGNd]].
pose proof Binary.Bmult_correct prec emax F1 F2 nan' BinarySingleNaN.mode_NE 
    (Binary.Bdiv prec emax F1 F2 nan BinarySingleNaN.mode_NE k' Nfr') Nbg'.
rewrite EQd in H0.
set (d' := Generic_fmt.round _ _ _ d) in H0,H3|-*.
assert (Hd'': (0 <= d' * IZR (Z.of_nat Nbg) <= IZR (Z.of_nat Nbg))%R). {
  clear - H3. split.  
  apply RIneq.Rmult_le_pos; try Lra.lra. 
 apply RIneq.IZR_le. lia.
 rewrite -{2}(Raxioms.Rmult_1_l (IZR _)).
 apply RIneq.Rmult_le_compat_r; try Lra.lra.
 apply RIneq.IZR_le. lia.
}
rewrite EQbg in H0.
set (d'' := (d' * _)%R) in Hd'', H0|-*.
rewrite Rlt_bool_true in H0.
2:{ clearbody d''; clear - Hd'' H1 .
  apply (Rabs_round_range d'' Nbg). rep_lia.  auto.
}
destruct H0 as [EQy [FINy SIGNy]].
change (Binary.Bmult _ _ _ _ _ _ _ _) with y in EQy, FINy, SIGNy.
rewrite FINd FINk FINbg /= in FINy.
split; auto.
rewrite {}EQy.
clearbody d'. clear EQd Hd d.
clearbody d''.
clear - Hd'' H1.
apply round_between_nats; try rep_lia; auto.
Qed.

End RDEF.


