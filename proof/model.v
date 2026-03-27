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
   θ0: ftype Tdouble
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
  waves: seq Wave.t
}.
End Data.
 
Section Floor.
Import BinarySingleNaN.

Definition BFLOOR (x : Binary.binary_float (fprec Tdouble) (femax Tdouble)) :=
match x with
| Binary.B754_finite _ _ s m e _ => BofZ _ _ (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble) 
                       (SFnearbyint_binary_aux (fprec Tdouble) mode_DN s m e)
| _ => x
end.
End Floor.

Definition M_PI : ftype Tdouble := 3.141592653589793%F64.

Definition L := BMULT (Zconst Tdouble 2) M_PI.

Definition range2pi (x: ftype Tdouble) : ftype Tdouble :=
    BMINUS x (BMULT L (BFLOOR (BDIV x L))).

Definition wrap (x: ftype Tdouble) : ftype Tdouble :=
   BMINUS (range2pi (BPLUS x M_PI)) M_PI.

Definition interp_aux (n Nfr: nat) (k: nat) : nat :=
  Z.to_nat (Binary.Btrunc _ _ (BFLOOR (BMULT (BDIV (Zconst _ (Z.of_nat k)) (Zconst _ (Z.of_nat Nfr))) 
                                                               (Zconst Tdouble (Z.of_nat n))))).

Lemma interp_aux1: forall n Nfr (k: 'I_Nfr.+1), is_true (leq (S (interp_aux n Nfr k)) (n.+1)).
Admitted.

Definition interpolate [n Nfr: nat] (y: 'rV[ftype Tdouble]_n.+1) (k: 'I_Nfr.+1) : ftype Tdouble :=
  let a := BMULT (BDIV (Zconst _ (Z.of_nat k)) (Zconst _ (Z.of_nat Nfr))) (Zconst Tdouble (Z.of_nat n)) in
  let j := Binary.Btrunc _ _ (BFLOOR a) in
  let j' := @Ordinal n.+1 (Z.to_nat j) (interp_aux1 n Nfr k) in
  (if  (Z.to_nat (j + 1) < n.+1)%N as b return (leq (S (Z.to_nat (j + 1))) n.+1 = b -> ftype Tdouble)
   then fun H0 :  (Z.to_nat (j + 1) < n.+1)%N = true => ((Zconst _ (j+1) - a) * y ord0 j' + (a-Zconst _ j) * y ord0 (Ordinal H0))%F64
   else fun=> y ord0 j') erefl.

Lemma getBG_col: forall (Nfr Nbg Nb: nat)  (k: 'I_Nfr.+1),
  let j := BMULT (BDIV (Zconst Tdouble (Z.of_nat k)) (Zconst Tdouble (Z.of_nat Nfr))) (Zconst Tdouble (Z.of_nat Nbg)) in
  let c := Z.to_nat (Binary.Btrunc _ _ j) in
  is_true (c < Nbg.+1)%N.
Admitted.

Definition Bexp : ftype Tdouble -> ftype Tdouble := FPCore.ff_func VSTlib.spec_math.MF.exp.

Definition waveform [Nfr Nb: nat] (dt: ftype Tdouble) (k: 'I_Nfr.+1)  (θw: ftype Tdouble * Wave.t) : 'cV[ftype Tdouble]_Nb.+1 :=
  let '(θ, w) := θw in
  let A := interpolate (Wave.A w) k in
  let σ := interpolate (Wave.σ w) k in
  \col_i 
   let dx := wrap (BMINUS (BMULT (Zconst Tdouble (Z.of_nat i)) (BDIV L (Zconst _ (Z.of_nat Nb.+1)))) θ) in
     BMULT A (Bexp (BOPP (BDIV (BMULT dx dx) (BMULT (Zconst _ 2) (BMULT σ σ))))).
 
Definition updateθ [Nfr: nat] (k: 'I_Nfr.+1) (dt: ftype Tdouble) (θw: ftype Tdouble * Wave.t) : ftype Tdouble * Wave.t :=
 let '(θ, w) := θw in
  let v := interpolate (Wave.v w) k in
 (BPLUS θ (BMULT v dt), w).

Fixpoint iterk [Nfr Nb Nbg : nat] (dt: ftype Tdouble) (BG :  'M[ftype Tdouble]_(Nb.+1,Nbg.+1)) 
          (X:  'M[ftype Tdouble]_(Nb.+1,Nfr.+1)) (k': nat)
         (θw: list (ftype Tdouble * Wave.t)) (energy diff_sum: ftype Tdouble) : ftype Tdouble := 
 match k' with
 | O => (diff_sum / energy)%F64
 | S k1 =>
      let k := @Ordinal Nfr.+1 (Nfr - k1.+1) (sub_ord_proof _ _) in
      let e_bg := col (Ordinal  (getBG_col Nfr Nbg Nb k)) BG in
      let θw' := if k == ord0 then θw else map (updateθ k dt) θw in
      let ew := map (waveform dt k) θw' in
      let e := foldl (F.addmx (n:=1)) e_bg ew in
      let energy' := \big[BPLUS/energy]_j BABS (X j k) in
      let d' := \big[BPLUS/diff_sum]_j BABS (BMINUS (X j k) (e j ord0)) in
      iterk dt BG X k1 θw' energy' d'
 end.

Definition synth_err (d: Data.t) : ftype Tdouble :=
 let '{| Data.Nb := Nb; Data.Nfr := Nfr; Data.Nbg := Nbg; Data.dt := dt; 
          Data.X := X; Data.BG := BG; Data.waves := waves |} := d in
   iterk dt BG X Nfr.+1 (zip (map Wave.θ0 waves) waves) (Zconst  _ 0) (Zconst _ 0).


