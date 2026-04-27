Require Import VST.floyd.functional_base.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require spec_math.
(*From LAProof.accuracy_proofs Require Import solve_model.*)
(*From LAProof.C Require Import (*densemat spec_alloc*)  floatlib matrix_model. *)
(* Require Import Coq.Classes.RelationClasses. *)

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

Module Wave.
Record t := {
   N: nat;
   A: 'rV[ftype Tdouble]_N.+1;
   σ: 'rV[ftype Tdouble]_N.+1;
   v: 'rV[ftype Tdouble]_N.+1;
   θ0: ftype Tdouble;
   Hn: Z.of_nat (N.+1) <= Int.max_signed
}.
End Wave. 

Module Data.
Record t := {
  Nb: nat;
  Nfr: nat;
  Nbg: nat;
  dt: ftype Tdouble;
  X: 'M[ftype Tdouble]_(Nb.+1,Nfr.+1);
  BG: 'M[ftype Tdouble]_(Nb.+1,Nbg.+1);
  waves: seq Wave.t;
  Hfr: Z.of_nat (Nb.+1 * Nfr.+1) <= Int.max_signed;
  Hbg: Z.of_nat (Nb.+1 * Nbg.+1) <= Int.max_signed
}.
End Data.
 
Section Floor.
Import BinarySingleNaN.

Axiom BFLOOR_nan :
  sig (fun x : float => eq (Binary.is_nan 53 1024 x) true).

Definition BFLOOR (x : Binary.binary_float (fprec Tdouble) (femax Tdouble)) : Binary.binary_float (fprec Tdouble) (femax Tdouble) 
  := Binary.BSN2B _ _ BFLOOR_nan
  (@BinarySingleNaN.Bnearbyint (fprec Tdouble) (femax Tdouble) (fprec_lt_femax Tdouble)  mode_DN 
   (Binary.B2BSN _ _ x)).

End Floor.

Definition M_PI : ftype Tdouble := 3.141592653589793%F64.

Definition L := BMULT (Zconst Tdouble 2) M_PI.

Definition range2pi (x: ftype Tdouble) : ftype Tdouble :=
    BMINUS x (BMULT L (BFLOOR (BDIV x L))).

Definition wrap (x: ftype Tdouble) : ftype Tdouble :=
   BMINUS (range2pi (BPLUS x M_PI)) M_PI.

Lemma Btrunc_range_pos: forall (lo hi: Z) (x: ftype Tdouble),
  (Int.min_signed <= lo)%Z ->
  (hi <= Int.max_signed)%Z ->
  (Zconst Tdouble lo <= x <= Zconst Tdouble Int.max_signed)%F64 ->
  Binary.is_finite x = true ->
  (lo <= Binary.Btrunc _ _ x < hi)%Z.
Admitted.

Lemma interpolate_range: forall [Nfr Nbg: nat]
    (H0: Z.of_nat (S Nfr) <= Int.max_signed)
    (H1: Z.of_nat (S Nbg) <= Int.max_signed)
   (k: 'I_Nfr.+1),
  let j := BMULT (BDIV (Zconst Tdouble (Z.of_nat k)) (Zconst Tdouble (Z.of_nat Nfr))) (Zconst Tdouble (Z.of_nat Nbg)) in
  Binary.is_finite j = true /\   (0 <= j <= Zconst Tdouble (Z.of_nat Nbg))%F64.
Admitted.

Definition interp_aux (n Nfr: nat) (k: nat) : nat :=
  Z.to_nat (Binary.Btrunc _ _ (BFLOOR (BMULT (BDIV (Zconst _ (Z.of_nat k)) (Zconst _ (Z.of_nat Nfr))) 
                                                               (Zconst Tdouble (Z.of_nat n))))).

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

Lemma Fle_Zconst: forall [t] (i j: Z), 
   (   - 2 ^ (fprec t)  <= i <= j)%Z -> 
    (j <= 2 ^ (fprec t)) -> 
 is_true (BCMP Gt false (Zconst t i) (Zconst t j)).
Proof.
intros.
unfold BCMP, Zconst, extend_comp.
destruct (BofZ_exact  (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) i ltac:(lia)) as [? [? ?]].
destruct (BofZ_exact  (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) j ltac:(lia)) as [? [? ?]].
rewrite (proof_irr (Pos2Z.is_pos (fprecp t)) (fprec_gt_0 t)).
rewrite Binary.Bcompare_correct; auto.
rewrite H1 H4.
rewrite Rcompare_IZR.
destruct (Z.compare_spec i j); auto. lia.
Qed.

Lemma BFLOOR_le: forall (x: ftype Tdouble), 
       is_true (Binary.is_finite x) -> is_true (BCMP Gt false (BFLOOR x) x).
Proof.
intros.
unfold BFLOOR.
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
rewrite Binary.B2R_B2BSN.
rewrite H0.
rewrite FIX.round_FIX_IZR.
rewrite Binary.B2R_B2BSN.
unfold BinarySingleNaN.round_mode.
set (y := Binary.B2R _ _ _).
pose proof Zfloor_lb y.
apply Rcompare_not_Gt in H4.
destruct (Rcompare _ _); try congruence.
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
unfold BCMP.
unfold extend_comp.
rewrite Binary.is_finite_BSN2B.
decompose [and] ( BinarySingleNaN.Bnearbyint_correct _ _ (fprec_lt_femax Tdouble)
     BinarySingleNaN.mode_DN
        (Binary.B2BSN (fprec Tdouble) (femax Tdouble) x)).
rewrite H2.
rewrite Binary.is_finite_B2BSN.
auto.
Qed.

Lemma interp_aux1: forall [Nfr n]  (Hfr: Z.of_nat (Nfr.+1)<=Int.max_signed) (Hn: Z.of_nat (n.+1) <= Int.max_signed) (k: 'I_Nfr.+1) ,
    is_true (leq (S (interp_aux n Nfr k)) (n.+1)).
Proof.
intros.
unfold interp_aux.
set (x := BMULT _ _).
destruct (interpolate_range Hfr Hn k).
fold x in H,H0. destruct H0. clearbody x.
pose proof Btrunc_range_pos 0 (Z.of_nat n.+1) (BFLOOR x) ltac:(rep_lia) ltac:(rep_lia).
spec H2; [ split | ].
-
clear - H H0.
apply BFLOOR_le'; auto.
compute; split; congruence.
-
apply Fle_trans with x; auto.
apply BFLOOR_le; auto.
apply Fle_trans with (Zconst Tdouble (Z.of_nat n)); auto.
apply Fle_Zconst.
simpl. clear - Hn. lia. simpl. clear. rep_lia.
-
spec H2. apply BFLOOR_finite; auto.
lia.
Qed.

Definition interpolate [n Nfr: nat] (Hfr: Z.of_nat (Nfr.+1)<=Int.max_signed) (Hn: Z.of_nat (n.+1) <= Int.max_signed)  (y: 'rV[ftype Tdouble]_n.+1) (k: 'I_Nfr.+1) : ftype Tdouble :=
  let a := BMULT (BDIV (Zconst _ (Z.of_nat k)) (Zconst _ (Z.of_nat Nfr))) (Zconst Tdouble (Z.of_nat n)) in
  let j := Binary.Btrunc _ _ (BFLOOR a) in
  let j' := @Ordinal n.+1 (Z.to_nat j) (interp_aux1 Hfr Hn k) in
  (if  (Z.to_nat (j + 1) < n.+1)%N as b return (leq (S (Z.to_nat (j + 1))) n.+1 = b -> ftype Tdouble)
   then fun H0 :  (Z.to_nat (j + 1) < n.+1)%N = true => ((Zconst _ (j+1) - a) * y ord0 j' + (a-Zconst _ j) * y ord0 (Ordinal H0))%F64
   else fun=> y ord0 j') erefl.

Lemma getBG_col: forall [Nfr Nbg: nat]
    (H0: Z.of_nat (S Nfr) <= Int.max_signed)
    (H1: Z.of_nat (S Nbg) <= Int.max_signed)
    (k: 'I_Nfr.+1),
  let j := BMULT (BDIV (Zconst Tdouble (Z.of_nat k)) (Zconst Tdouble (Z.of_nat Nfr))) (Zconst Tdouble (Z.of_nat Nbg)) in
  let c := Z.to_nat (Binary.Btrunc _ _ j) in
  is_true (c < Nbg.+1)%N.
Proof.
intros.
destruct (interpolate_range H0 H1 k) as [Hj ?H].
fold j in Hj,H.
clearbody j.
pose proof (Btrunc_range_pos 0 (Z.of_nat Nbg) j ltac:(rep_lia) ltac:(rep_lia)).
subst c.
set (i := Binary.Btrunc _ _ j) in H,H2|-*. clearbody i.
destruct H.
spec H2; [ | lia].
split; auto.
clear - H3 H1.
eapply Fle_trans; try eassumption.
apply Fle_Zconst.
simpl. lia.
simpl.
rep_lia.
Qed.

Definition Bexp : ftype Tdouble -> ftype Tdouble := FPCore.ff_func VSTlib.spec_math.MF.exp.

Definition waveform [Nfr Nb: nat] (Hfr: Z.of_nat (Nfr.+1)<=Int.max_signed) (Hnb: Z.of_nat (Nb.+1) <= Int.max_signed) 
     (dt: ftype Tdouble) (k: 'I_Nfr.+1)  (θw: Values.val * Wave.t) : 'cV[ftype Tdouble]_Nb.+1 :=
 match θw with
 | (Vfloat θ, w) => 
  let A := interpolate Hfr (Wave.Hn w) (Wave.A w) k in
  let σ := interpolate Hfr (Wave.Hn w) (Wave.σ w) k in
  \col_i 
   let dx := wrap (BMINUS (BMULT (Zconst Tdouble (Z.of_nat i)) (BDIV L (Zconst _ (Z.of_nat Nb.+1)))) θ) in
     BMULT A (Bexp (BOPP (BDIV (BMULT dx dx) (BMULT (Zconst _ 2) (BMULT σ σ)))))
 | _ => const_mx (Zconst _ 0)
 end.
 
Definition updateθ [Nfr: nat] (Hfr: Z.of_nat (Nfr.+1)<=Int.max_signed)  (k: 'I_Nfr.+1) (dt: ftype Tdouble) (θw: Values.val * Wave.t) : Values.val * Wave.t :=
 match θw with
 | (Vfloat θ, w) =>
  let v := interpolate  Hfr (Wave.Hn w) (Wave.v w) (@inord Nfr (k-1)%N) in
   (Vfloat (range2pi (@BPLUS _ Tdouble θ (BMULT v dt))), w)
 | (_, w) => (Vundef, w)
 end.

Definition one_iterk  [Nfr Nb Nbg : nat] 
    (H0: Z.of_nat (S Nfr) <= Int.max_signed)
    (Hb: Z.of_nat (S Nb) <= Int.max_signed)
    (H1: Z.of_nat (S Nbg) <= Int.max_signed) 
   (dt: ftype Tdouble) (BG :  'M[ftype Tdouble]_(Nb.+1,Nbg.+1)) 
          (X:  'M[ftype Tdouble]_(Nb.+1,Nfr.+1)) :
     (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) ->
      ('I_Nfr.+1) ->
     (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) :=
fun '(θw, (energy, diff_sum)) k =>
  let e_bg := col (Ordinal  (getBG_col H0 H1 k)) BG
  in let θw' := if k==ord0 
                 then map (fun w => (Vfloat (Wave.θ0 (snd w)), snd w)) θw
                 else map (updateθ H0 k dt) θw
  in let ew := map (waveform H0 Hb dt k) θw'
  in let e := foldl (F.addmx (n:=1)) e_bg ew
  in let energy' := foldl BPLUS energy (map (fun j => BABS (X j k)) (ord_enum Nb.+1))
  in let d' := foldl BPLUS diff_sum (map (fun j => BABS (BMINUS (X j k) (e j ord0))) (ord_enum Nb.+1))
  in (θw', (energy', d')).

(*
Definition a_nan : ftype Tdouble := proj1_sig (FPCore.any_nan (fprec Tdouble) (femax Tdouble) (fprec_gt_one Tdouble)).

Lemma a_nan_is_nan: Binary.is_nan _ _ a_nan.
Proof. unfold a_nan.
  destruct (FPCore.any_nan _ _ _); auto.
Qed.
*)

Definition initial_values (waves: list Wave.t) :  (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) :=
 (map (fun w => (Vundef, w)) waves, (Zconst _ 0, Zconst _ 0)).

Definition iterk [Nfr Nb Nbg : nat] 
    (H0: Z.of_nat (S Nfr) <= Int.max_signed)
    (Hb: Z.of_nat (S Nb) <= Int.max_signed)
    (H1: Z.of_nat (S Nbg) <= Int.max_signed)
   (dt: ftype Tdouble) (BG :  'M[ftype Tdouble]_(Nb.+1,Nbg.+1)) 
          (X:  'M[ftype Tdouble]_(Nb.+1,Nfr.+1)) (waves: list Wave.t) (k: nat) : 
     (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) :=
 foldl (one_iterk H0 Hb H1 dt BG X) (initial_values waves) (firstn k (ord_enum Nfr.+1)).

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

Definition one_iteri  [Nfr Nb Nbg : nat] 
    (H0: Z.of_nat (S Nfr) <= Int.max_signed)
    (Hb: Z.of_nat (S Nb) <= Int.max_signed)
    (H1: Z.of_nat (S Nbg) <= Int.max_signed)
    (dt: ftype Tdouble) (BG :  'M[ftype Tdouble]_(Nb.+1,Nbg.+1)) 
          (X:  'M[ftype Tdouble]_(Nb.+1,Nfr.+1)) (k: 'I_Nfr.+1) :
     (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) -> 'I_Nb.+1 ->
     (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) :=
 fun '(θw, (energy, diff_sum)) (i: 'I_Nb.+1) =>
   let θw' := if i==ord0
                   then if k==ord0 
                         then map (fun w => (Vfloat (Wave.θ0 (snd w)), snd w)) θw
                         else map (updateθ H0 k dt) θw
                   else θw
    in let ew : seq (ftype Tdouble) := map (fun f: 'cV_Nb.+1 => f i ord0) (map (waveform H0 Hb dt k) θw') 
    in let e_bg := BG i (Ordinal (getBG_col H0 H1 k))
    in let e : ftype Tdouble:= foldl BPLUS e_bg ew
    in let Xik := X i k
    in let energy' := BPLUS energy (BABS Xik)
    in let d' := BPLUS diff_sum (BABS (BMINUS Xik e))
    in (θw', (energy', d')).

Definition all_iteri: forall  [Nfr Nb Nbg : nat] 
    (Hfr: Z.of_nat (S Nfr) <= Int.max_signed)
    (Hb: Z.of_nat (S Nb) <= Int.max_signed)
    (Hbg: Z.of_nat (S Nbg) <= Int.max_signed)
    (dt: ftype Tdouble) (BG :  'M[ftype Tdouble]_(Nb.+1,Nbg.+1)) 
          (X:  'M[ftype Tdouble]_(Nb.+1,Nfr.+1)) (k: 'I_Nfr.+1) (state: list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)),
   foldl (one_iteri Hfr Hb Hbg dt BG X k) state (ord_enum Nb.+1) = one_iterk Hfr Hb Hbg dt BG X state k.
Proof.
intros.
unfold one_iterk.
destruct state as [θw [energy diff_sum]].
set u := if _ then _ else _.
rewrite -(firstn_skipn 1 (ord_enum (S Nb))).
destruct (ord_enum (S Nb)) eqn:?H; [pose proof (mv_mathcomp.size_ord_enum (S Nb)); rewrite H in H0; inv H0 |].
simpl.
assert (forallb (fun i => negb (eq_op i ord0)) l = true). {
 rewrite forallb_forall. intros.
 assert (in_mem x (mem l)) by (apply /Iter.In_mem; auto).
 clear H0; rename H1 into H0.
 pose proof ord_enum_uniq (S Nb).
 rewrite H cons_uniq in H1. 
 red in H1; rewrite andb_true_iff in H1; destruct H1 as [H1 _].
 pose proof mv_mathcomp.nth_ord_enum' (S Nb) ord0 ord0.
 rewrite H in H2. simpl in H2. subst o.
 apply /eqP. intro; subst.  rewrite H0 in H1. discriminate.
}
pose proof mv_mathcomp.nth_ord_enum' (S Nb) ord0 ord0. rewrite H in H1. simpl in H1. subst o.
rewrite eq_refl.
clear H.
fold u.
set e1 := BPLUS energy _. clearbody e1.
set f := map (waveform _ _ _ _) _.
replace (fun_of_matrix (foldl (F.addmx (n:=1)) (col (Ordinal (getBG_col Hfr Hbg k)) BG) f)
          ord0 ord0)
 with (foldl BPLUS (fun_of_matrix BG ord0 (Ordinal (getBG_col Hfr Hbg k)))
                       (map
                          (fun f0 : matrix (ftype Tdouble) (S Nb) 1 =>
                           fun_of_matrix f0 ord0 ord0)
                          f)).
2:{
clear.
rewrite -(revK f).
rewrite map_rev.
rewrite !foldl_rev.
induction (rev f).
rewrite mxE //.
rewrite /= IHl !mxE //.
}
set d1 := BPLUS diff_sum _.
clearbody d1.
revert H0.
rewrite -(revK l).
set (r := rev l).
clearbody r. clear l.
rewrite !map_rev.
rewrite forallb_rev.
rewrite !foldl_rev.
induction r; simpl; intros; auto.
rewrite andb_true_iff in H0; destruct H0.
specialize (IHr H0). clear H0.
rewrite {}IHr.
unfold one_iteri.
destruct (a == ord0); try discriminate. clear H.
f_equal.
f_equal.
f_equal.
f_equal.
f_equal.
subst u.
fold f.
clearbody f.
rewrite -(revK f).
clear r.
set r := rev f. rewrite map_rev. rewrite !foldl_rev.
clearbody r.
induction r; rewrite ?mxE // -IHr //.
Qed.

Lemma N_range: forall [Nb N] (H: Z.of_nat (S Nb * S N) <= Int.max_signed),
        Z.of_nat (S N) <= Int.max_signed.
Proof. rep_lia. Qed.

Lemma N_range1: forall [Nb N] (H: Z.of_nat (S Nb * S N) <= Int.max_signed),
        Z.of_nat (S Nb) <= Int.max_signed.
Proof. rep_lia. Qed.

Definition synth_err (d: Data.t) : ftype Tdouble :=
  let '(_, (energy, diff_sum)) := iterk (N_range (Data.Hfr d)) (N_range1 (Data.Hfr d)) (N_range (Data.Hbg d)) (Data.dt d) (Data.BG d) (Data.X d) (Data.waves d) (Data.Nfr d).+1
   in  (diff_sum / energy)%F64.




