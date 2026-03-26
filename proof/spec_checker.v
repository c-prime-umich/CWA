(** * CWA.spec_checker:  VST function specification for CWA checker *)

(* begin details : Require Imports and Open Scope, etc. *)
Require Import VST.floyd.proofauto.
From CWA Require Import checker model.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require Import spec_math spec_malloc.
From LAProof.C Require Import floatlib matrix_model.
Require Import Coq.Classes.RelationClasses.

From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
Import fintype matrix.
Import Rdefinitions.

Require LAProof.accuracy_proofs.export.
Module F := LAProof.accuracy_proofs.mv_mathcomp.F.

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.
Delimit Scope R_scope with Re.

(* end details *)

Definition tdata := Tstruct _Data noattr.
Definition twave := Tstruct _Wave noattr.

Definition wave_rep' (sh: share) (wx: wave * (val*val*val)) (p: val) : mpred :=
  let '(w, (Ap, sigmap, vp)) := wx in
   data_at sh twave (Ap, (sigmap, (vp, (Vint (Int.repr (Wave_N w)), Vfloat (Wave_θ0 w))))) p
 * data_at sh (tarray tdouble (Zlength (Wave_A w))) (map Vfloat (Wave_A w)) sigmap
 * data_at sh (tarray tdouble (Zlength (Wave_σ w))) (map Vfloat (Wave_σ w)) sigmap
 * data_at sh (tarray tdouble (Zlength (Wave_v w))) (map Vfloat (Wave_v w)) vp.

Definition wave_rep (sh: share) (w: wave) (p: val) : mpred :=
 EX wxp: val*val*val, wave_rep' sh (w,wxp) p.

Lemma wave_rep'_valid_pointer: forall sh wx p, 
   sepalg.nonidentity sh ->
   wave_rep' sh wx p |-- valid_pointer p.
Proof.
intros. unfold wave_rep'. destruct wx as [? [[? ?] ?]].
rewrite !sepcon_assoc.
eapply derives_trans; [apply sepcon_derives; [ | apply derives_refl] | ].
apply data_at_valid_ptr; simpl; auto; lia.
entailer!!.
Qed.

Lemma wave_rep_valid_pointer: forall sh w p, 
   sepalg.nonidentity sh ->
   wave_rep sh w p |-- valid_pointer p.
Proof.
intros. unfold wave_rep. Intros wxp.  apply wave_rep'_valid_pointer; auto. 
Qed.

#[export] Hint Resolve wave_rep'_valid_pointer wave_rep_valid_pointer: valid_pointer.

Definition wx_to_waverep (wx: wave * (val*val*val)) : val * (val * (val * (val * val))) :=
  let '(w, (Ap, sigmap, vp)) := wx in
  (Ap, (sigmap, (vp, (Vint (Int.repr (Wave_N w)), Vfloat (Wave_θ0 w))))).

Definition data_rep (sh: share) (d: data) (p: val) : mpred :=
 EX Xp: val, EX Bp: val, EX wp: val, EX wx: list (wave*(val*val*val)),
  !! (map fst wx = Data_waves d) &&
  data_at sh tdata (Xp, (Bp, (Vint (Int.repr (Data_Nb d)), (Vint (Int.repr (Data_Nfr d)), (Vint (Int.repr (Data_Nbg d)),
                                 (Vfloat (Data_dt d), (map wx_to_waverep wx, Vint (Int.repr (Zlength (Data_waves d)))))))))) p 
 * data_at sh (tarray tdouble (Zlength (Data_XT d))) (map Vfloat (Data_XT d)) Xp
 * data_at sh (tarray tdouble (Zlength (Data_BG d))) (map Vfloat (Data_BG d)) Bp.

Definition range2pi_spec :=
  DECLARE _range2pi
  WITH x: ftype Tdouble
  PRE [ tdouble ]
    PROP ()
    PARAMS (Vfloat x)
    SEP()
  POST [ tdouble ]
    PROP ()
    RETURN (Vfloat (range2pi x))
    SEP().


Definition wrap_spec :=
  DECLARE _wrap
  WITH x: ftype Tdouble
  PRE [ tdouble ]
    PROP ()
    PARAMS (Vfloat x)
    SEP()
  POST [ tdouble ]
    PROP ()
    RETURN (Vfloat (wrap x))
    SEP().


Definition interpolate_spec :=
  DECLARE _interpolate
  WITH sh: share, f: ftype Tdouble, y: list (ftype Tdouble), yp: val, k: ftype Tdouble
  PRE [ tdouble , tptr tdouble, tdouble ]
    PROP (readable_share sh; (0 < FT2R f)%Re; (0 <= FT2R k / FT2R f <= IZR (Zlength y))%Re)
    PARAMS (Vfloat f; yp; Vfloat k)
    SEP(data_at sh (tarray tdouble (Zlength y)) (map Vfloat y) yp)
  POST [ tdouble ]
    PROP ()
    RETURN (Vfloat (interpolate f y k))
    SEP(data_at sh (tarray tdouble (Zlength y)) (map Vfloat y) yp).

Definition synthesize_spec :=
  DECLARE _synthesize
  WITH sh: share, p : val, d: data
  PRE [ tptr tdata ]
    PROP(readable_share sh)
    PARAMS(p)
    SEP(data_rep sh d p)
  POST[ tint ]
    PROP()
    RETURN (Vfloat (synth_err d))
    SEP(data_rep sh d p).




