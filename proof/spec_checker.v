(** * CWA.spec_checker:  VST function specification for CWA checker *)

(* begin details : Require Imports and Open Scope, etc. *)
Require Import VST.floyd.proofauto.
From CWA Require Import checker model.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require Import spec_math spec_malloc.
From LAProof.C Require Import floatlib matrix_model spec_densemat.
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

Definition wave_rep' (sh: share) (wx: Wave.t * (val*val*val)) (p: val) : mpred :=
  let '(w, (Ap, σp, vp)) := wx in
   data_at sh twave (Ap, (σp, (vp, (Vint (Int.repr (Z.of_nat (S (Wave.N w)))), Vfloat (Wave.θ0 w))))) p
 * densematn sh (map_mx Some (Wave.A w)) Ap
 * densematn sh (map_mx Some (Wave.σ w)) σp
 * densematn sh (map_mx Some (Wave.v w)) vp.

Definition wave_rep (sh: share) (w: Wave.t) (p: val) : mpred :=
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

Definition wx_to_waverep (wx: Wave.t * (val*val*val)) : val * (val * (val * (val * val))) :=
  let '(w, (Ap, sigmap, vp)) := wx in
  (Ap, (sigmap, (vp, (Vint (Int.repr (S (Wave.N w))), Vfloat (Wave.θ0 w))))).

Definition data_rep (sh: share) (d: Data.t) (p: val) : mpred :=
 EX Xp: val, EX Bp: val, EX wp: val, EX wx: list (Wave.t*(val*val*val)),
  !! (map fst wx = Data.waves d) &&
  data_at sh tdata (Xp, (Bp, (Vint (Int.repr (Data.Nb d)), (Vint (Int.repr (Data.Nfr d)), (Vint (Int.repr (Data.Nbg d)),
                                 (Vfloat (Data.dt d), (map wx_to_waverep wx, Vint (Int.repr (Zlength (Data.waves d)))))))))) p 
 * densematn sh (map_mx Some (Data.X d)) Xp
 * densematn sh (map_mx Some (Data.BG d)) Bp.

Definition floor_spec :=  (* really should get this from mathlib *)
 DECLARE _floor
 WITH x: ftype Tdouble
 PRE [ tdouble ]
  PROP()
  PARAMS (Vfloat x)
  SEP()
 POST [ tdouble ]
   PROP()
   RETURN(Vfloat (BFLOOR x))
   SEP().

Definition exp_spec := (* really should get this from mathlib *)
 DECLARE _exp
 WITH x: ftype Tdouble
 PRE [ tdouble ]
  PROP()
  PARAMS (Vfloat x)
  SEP()
 POST [ tdouble ]
   PROP()
   RETURN(Vfloat (Bexp x))
   SEP().


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
  WITH sh: share, Y: {Nt: nat &  'rV[ftype Tdouble]_(S Nt)}, yp: val, K: {Nfr & 'I_(S Nfr)}
  PRE [ tint, tint, tptr tdouble, tdouble ] let (Nt,y) := Y in let (Nfr,k) := K in 
    PROP (readable_share sh)
    PARAMS (Vint (Int.repr(S Nfr)); Vint (Int.repr(S Nt)); yp; Vfloat (Zconst Tdouble (nat_of_ord k)))
    SEP(densematn sh (map_mx Some y) yp)
  POST [ tdouble ] let (Nt,y) := Y in let (Nfr,k) := K in 
    PROP ()
    RETURN (Vfloat (interpolate y k))
    SEP(densematn sh (map_mx Some y) yp).

Definition synthesize_spec :=
  DECLARE _synthesize
  WITH sh: share, p : val, d: Data.t
  PRE [ tptr tdata ]
    PROP(readable_share sh)
    PARAMS(p)
    SEP(data_rep sh d p)
  POST[ tint ]
    PROP()
    RETURN (Vfloat (synth_err d))
    SEP(data_rep sh d p).




