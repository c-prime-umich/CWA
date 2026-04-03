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

Lemma getBG_col: forall (Nfr Nbg: nat)  (k: 'I_Nfr.+1),
  let j := BMULT (BDIV (Zconst Tdouble (Z.of_nat k)) (Zconst Tdouble (Z.of_nat Nfr))) (Zconst Tdouble (Z.of_nat Nbg)) in
  let c := Z.to_nat (Binary.Btrunc _ _ j) in
  is_true (c < Nbg.+1)%N.
Admitted.

Definition Bexp : ftype Tdouble -> ftype Tdouble := FPCore.ff_func VSTlib.spec_math.MF.exp.

Definition waveform [Nfr Nb: nat] (dt: ftype Tdouble) (k: 'I_Nfr.+1)  (θw: Values.val * Wave.t) : 'cV[ftype Tdouble]_Nb.+1 :=
 match θw with
 | (Vfloat θ, w) => 
  let A := interpolate (Wave.A w) k in
  let σ := interpolate (Wave.σ w) k in
  \col_i 
   let dx := wrap (BMINUS (BMULT (Zconst Tdouble (Z.of_nat i)) (BDIV L (Zconst _ (Z.of_nat Nb.+1)))) θ) in
     BMULT A (Bexp (BOPP (BDIV (BMULT dx dx) (BMULT (Zconst _ 2) (BMULT σ σ)))))
 | _ => const_mx (Zconst _ 0)
 end.
 
Definition updateθ [Nfr: nat] (k: 'I_Nfr.+1) (dt: ftype Tdouble) (θw: Values.val * Wave.t) : Values.val * Wave.t :=
 match θw with
 | (Vfloat θ, w) =>
  let v := interpolate (Wave.v w) (@inord Nfr (k-1)%N) in
   (Vfloat (range2pi (@BPLUS _ Tdouble θ (BMULT v dt))), w)
 | (_, w) => (Vundef, w)
 end.

Definition one_iterk  [Nfr Nb Nbg : nat] (dt: ftype Tdouble) (BG :  'M[ftype Tdouble]_(Nb.+1,Nbg.+1)) 
          (X:  'M[ftype Tdouble]_(Nb.+1,Nfr.+1)) :
     (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) ->
      ('I_Nfr.+1) ->
     (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) :=
fun '(θw, (energy, diff_sum)) k =>
  let e_bg := col (Ordinal  (getBG_col Nfr Nbg k)) BG
  in let θw' := if k==ord0 
                 then map (fun w => (Vfloat (Wave.θ0 (snd w)), snd w)) θw
                 else map (updateθ k dt) θw
  in let ew := map (waveform dt k) θw'
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

Definition iterk [Nfr Nb Nbg : nat] (dt: ftype Tdouble) (BG :  'M[ftype Tdouble]_(Nb.+1,Nbg.+1)) 
          (X:  'M[ftype Tdouble]_(Nb.+1,Nfr.+1)) (waves: list Wave.t) (k: nat) : 
     (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) :=
 foldl (one_iterk dt BG X) (initial_values waves) (firstn k (ord_enum Nfr.+1)).

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

Definition one_iteri  [Nfr Nb Nbg : nat] (dt: ftype Tdouble) (BG :  'M[ftype Tdouble]_(Nb.+1,Nbg.+1)) 
          (X:  'M[ftype Tdouble]_(Nb.+1,Nfr.+1)) (k: 'I_Nfr.+1) :
     (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) -> 'I_Nb.+1 ->
     (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) :=
 fun '(θw, (energy, diff_sum)) (i: 'I_Nb.+1) =>
   let θw' := if i==ord0
                   then if k==ord0 
                         then map (fun w => (Vfloat (Wave.θ0 (snd w)), snd w)) θw
                         else map (updateθ k dt) θw
                   else θw
    in let ew : seq (ftype Tdouble) := map (fun f: 'cV_Nb.+1 => f i ord0) (map (waveform dt k) θw') 
    in let e_bg := BG i (Ordinal (getBG_col Nfr Nbg k))
    in let e : ftype Tdouble:= foldl BPLUS e_bg ew
    in let Xik := X i k
    in let energy' := BPLUS energy (BABS Xik)
    in let d' := BPLUS diff_sum (BABS (BMINUS Xik e))
    in (θw', (energy', d')).

Definition all_iteri: forall  [Nfr Nb Nbg : nat] (dt: ftype Tdouble) (BG :  'M[ftype Tdouble]_(Nb.+1,Nbg.+1)) 
          (X:  'M[ftype Tdouble]_(Nb.+1,Nfr.+1)) (k: 'I_Nfr.+1) (state: list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)),
   foldl (one_iteri dt BG X k) state (ord_enum Nb.+1) = one_iterk dt BG X state k.
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
set f := map (waveform _ _) _.
replace (fun_of_matrix (foldl (F.addmx (n:=1)) (col (Ordinal (getBG_col Nfr Nbg k)) BG) f)
          ord0 ord0)
 with (foldl BPLUS (fun_of_matrix BG ord0 (Ordinal (getBG_col Nfr Nbg k)))
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

Definition synth_err (d: Data.t) : ftype Tdouble :=
 let '{| Data.Nb := Nb; Data.Nfr := Nfr; Data.Nbg := Nbg; Data.dt := dt; 
          Data.X := X; Data.BG := BG; Data.waves := waves |} := d in
  let '(_, (energy, diff_sum)) := iterk dt BG X waves Nfr.+1
   in  (diff_sum / energy)%F64.


