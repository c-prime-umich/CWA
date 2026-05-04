Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require Import spec_math spec_malloc.
From LAProof Require Import spec_densemat densemat_lemmas.
From CWA Require Import checker model spec_checker.

From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
Import fintype matrix.

Require LAProof.accuracy_proofs.export.
Module F := LAProof.accuracy_proofs.mv_mathcomp.F.
Require Import CWA.float_lemmas.

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition Gprog := [ densematn_get_spec; floor_spec; exp_spec; fabs_spec;
                               range2pi_spec; wrap_spec; interpolate_spec; synthesize_spec].

Ltac is_float_const A := 
   lazymatch A with
   | Zconst _ _ => idtac 
   | Float.of_bits _  => idtac
   | b64_B754_finite _ _ _ _ => idtac 
   end.

Ltac equal_float_constants :=
lazymatch goal with |- @eq ?t ?A ?B =>
  let t' := eval hnf in t in 
  lazymatch t' with Binary.binary_float _ _ => idtac 
  | _ => fail "Ltac equal_float_constants works only on equalities of type binary_float, instead got" t
  end;
  is_float_const A;
  is_float_const B;
  with_strategy transparent [Float.of_bits]
      (let a := eval hnf in A in let b := eval hnf in B in change (a=b));
   try solve [f_equal; apply proof_irr];
   fail "Ltac equal_float_constants found seemingly unequal values" A "and" B
 | |- _ => fail "Ltac equal_float_constants works only on equalities of type binary_float"
end.

Lemma Float_to_int_e: forall x i, Float.to_int x = Some i -> Zoffloat x = Some (Int.signed i).
Proof.
intros.
with_strategy transparent [Float.to_int] unfold Float.to_int in H.
unfold Zoffloat.
destruct x; try discriminate.
inv H. reflexivity.
unfold lib.IEEE754_extra.ZofB_range, lib.IEEE754_extra.ZofB in H.
destruct e;  destruct (_ && _)%bool  eqn:H0; try destruct s; inv H;
 try (rewrite andb_true_iff in H0; destruct H0); simpl in *;
rewrite Int.signed_repr; auto; try rep_lia.
Qed.

Lemma Float_of_int_e: forall k,
  Int.min_signed <= k <= Int.max_signed ->
  Float.of_int (Int.repr k) = Zconst Tdouble k.
Proof. 
 intros.
  with_strategy transparent [Float.of_int] unfold Float.of_int;
 rewrite Int.signed_repr by rep_lia;
  unfold Zconst;  unfold lib.IEEE754_extra.BofZ, BofZ; f_equal; auto.
Qed.

Ltac prove_float_exprs_equal :=   
repeat first [ simple apply eq_refl
                   | simple apply f_equal2
                   | simple apply f_equal
                   | apply (f_equal2 (@BPLUS nans Tdouble))
                   | apply (f_equal2 (@BMINUS nans Tdouble))
                   | apply (f_equal2 (@BMULT nans Tdouble))
                   | apply (f_equal2 (@BDIV nans Tdouble))
                   | apply (f_equal (@BOPP nans Tdouble))
                   | simple apply Float_of_int_e; rep_lia
                   | equal_float_constants
                   | reflexivity
                   ].

Lemma body_range2pi: semax_body Vprog Gprog f_range2pi range2pi_spec.
Proof.
start_function.
forward_call.
forward.
entailer!!.
f_equal.
unfold range2pi, L, M_PI.
prove_float_exprs_equal.
Qed.

Lemma body_wrap: semax_body Vprog Gprog f_wrap wrap_spec.
Proof.
start_function.
forward_call.
forward.
entailer!!.
f_equal.
unfold wrap, M_PI.
with_strategy opaque [range2pi] prove_float_exprs_equal.
Qed.

Definition synthesize_i_loop : statement :=
 ltac:(let body := constr:(fn_body f_synthesize) in let body := eval simpl in body in 
 match body with context [ Ssequence (Sset _i (Econst_int ?z ?t)) ?B ] =>
  exact (Ssequence (Sset _i (Econst_int z t)) B)
 end).

Definition synthesize_w_loop : statement :=
 ltac:(let body := constr:(fn_body f_synthesize) in let body := eval simpl in body in 
 match body with context [ Ssequence (Sset _w (Econst_int ?z ?t)) ?B ] =>
  exact (Ssequence (Sset _w (Econst_int z t)) B)
 end).

Definition synthesize_ifthen : statement :=
 ltac:(let body := constr:(fn_body f_synthesize) in let body := eval simpl in body in 
 match body with context [ Sifthenelse (Ebinop Oeq (Etempvar _i tint) 
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint) ?Then ?Else ] =>
  exact (Sifthenelse  (Ebinop Oeq (Etempvar _i tint) 
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint) Then Else)
 end).

Lemma mk_ord [n: nat] [k: Z] (Hk: 0 <= k < Z.of_nat n):  Datatypes.is_true (ssrnat.leq (S (Z.to_nat k)) n).
Proof.
intros.
unfold ssrnat.leq. unfold eqtype.eq_op. simpl. 
destruct (@ssrnat.eqnP (ssrnat.subn (S (Z.to_nat k)) n) O); hnf; auto.
rewrite ssrnat.subnE in n0. lia.
Qed.

Lemma Znth_ord_enum: forall [n: nat] [d] [k: Z] (Hk: Datatypes.is_true (ssrnat.leq (S (Z.to_nat k)) n)) (H: 0 <= k),
   @Znth _ d k (ord_enum n) = Ordinal Hk.
Proof.
intros.
apply ord_inj; simpl.
rewrite <- nth_Znth  by (rewrite Zlength_correct, mv_mathcomp.size_ord_enum; lia). 
rewrite <- mv_mathcomp.nth_List_nth.
change (Z.to_nat k) with (nat_of_ord (Ordinal Hk)).
rewrite mv_mathcomp.nth_ord_enum'.
auto.
Qed.

Section FtoInt.
Import Rdefinitions.

Lemma Float_to_int_i_aux: 
 forall (x : ftype Tdouble),
  Binary.is_finite x = true ->
  Rle (IZR (- (2147483648))) (FT2R x) /\
  Rle (FT2R x) (IZR (2147483648 - 1)) ->
  lib.IEEE754_extra.ZofB_range 53 1024 x (- (2147483648)) (2147483648 - 1) =
  Some (Binary.Btrunc (fprec Tdouble) (femax Tdouble) x).
Proof.
intros.
unfold lib.IEEE754_extra.ZofB_range.
change lib.IEEE754_extra.ZofB with ZofB.
destruct x; try discriminate H; try reflexivity.
clear H.
rewrite ZofB_correct.
simpl Binary.is_finite. cbv match.
unfold FT2R in H0.
set (x := Binary.B2R _ _ _) in *.
match goal with |- context [andb ?A ?B] => assert (andb A B = true) end.
-
destruct H0.
rewrite andb_true_iff; split.
+ clear H0. apply Zaux.Zle_bool_true.
apply Zfloor_lub in H.
unfold Ztrunc.
destruct (Rlt_bool x 0) eqn:?H; auto.
transitivity (Zfloor x); auto.
destruct (RIneq.Req_dec_T  (IZR (Zfloor x)) x ).
*
apply RIneq.le_IZR.
rewrite e1.
apply Zceil_ub.
*
rewrite Zceil_floor_neq by auto.
lia.
+
clear H.  apply Zaux.Zle_bool_true.
unfold  Ztrunc.
destruct (Rlt_bool x 0) eqn:?H; auto.
apply Zceil_glb. auto.
apply RIneq.le_IZR.
eapply RIneq.Rle_trans.
apply Zfloor_lb.
auto.
-
rewrite H.
f_equal.
apply RIneq.eq_IZR.
rewrite Binary.Btrunc_correct by reflexivity.
fold x.
rewrite FIX.round_FIX_IZR.
auto.
Qed.

Lemma Float_to_int_i: forall x: ftype Tdouble,
  Binary.is_finite x = true ->
  Rle (IZR Int.min_signed) (FT2R x) /\
              Rle (FT2R x) (IZR Int.max_signed) ->
 Float.to_int x = Some (Int.repr (Binary.Btrunc (fprec Tdouble) (femax Tdouble) x)).
Proof.
intros.
with_strategy transparent [Float.to_int] unfold Float.to_int.
unfold Int.min_signed , Int.max_signed in *.
let z := constr:(Int.half_modulus) in let z' := eval compute in z in change z with z' in *.
rewrite (Float_to_int_i_aux x H H0).
auto.
Qed.

Lemma Binary_Btrunc_Zoffloat: forall x i, Zoffloat x = Some i -> Binary.Btrunc _ _ x = i.
Proof.
intros.
unfold Zoffloat in H.
destruct x; try discriminate.
inv H; reflexivity.
apply RIneq.eq_IZR.
rewrite Binary.Btrunc_correct by reflexivity.
rewrite FIX.round_FIX_IZR.
f_equal.
simpl.
unfold Defs.F2R; simpl.
destruct e; inv H; simpl.
-
simpl.
rewrite RIneq.Rmult_1_r.
unfold SpecFloat.cond_Zopp.
unfold Ztrunc.
destruct s; simpl.
rewrite Rlt_bool_true.
apply Zceil_IZR.
unfold IZR.
pose proof (RIneq.IPR_gt_0 m); Lra.lra.
rewrite Rlt_bool_false.
apply Zfloor_IZR.
unfold IZR.
pose proof (RIneq.IPR_gt_0 m); Lra.lra.
-
rewrite <- RIneq.mult_IZR.
rewrite Ztrunc_IZR.
reflexivity.
-
pose proof Zpow_facts.Zpower_pos_pos 2 p ltac:(lia).
destruct (Z.pow_pos 2 p); try lia. clear H.
pose proof BinInt.Z.pos_div_eucl_bound m (Z.pos p0) ltac:(lia).
pose proof Z.pos_div_eucl_eq m (Z.pos p0) ltac:(lia).
destruct (Z.pos_div_eucl m (Z.pos p0)).
simpl in H.
assert (0 <= z) by nia.
rewrite H0; clear H0 m e0.
simpl in H.
destruct s; simpl.
+ rewrite RIneq.opp_IZR. rewrite <- RIneq.Ropp_mult_distr_l. 
rewrite Ztrunc_opp.
f_equal.
etransitivity.
apply Ztrunc_div.
lia.
rewrite Z.quot_add_l; try lia.
rewrite Z.quot_small; try lia.
+
etransitivity.
apply Ztrunc_div.
lia.
rewrite Z.quot_add_l; try lia.
rewrite Z.quot_small; try lia.
Qed.

End FtoInt.

Lemma bg_col_is: forall [Nfr k] Nbg 
    (H: 0 <= k < Z.of_nat (S Nfr))
    (H0: 1 < Z.of_nat (S Nfr) <= Int.max_signed)
    (H1: Z.of_nat (S Nbg) <= Int.max_signed)
    (Hk: Datatypes.is_true (ssrnat.leq (S (Z.to_nat k)) (S Nfr))),
     Float.to_int
        (Float.mul
           (Float.div (Float.of_int (Int.repr k))
              (Float.of_int (Int.repr (Z.of_nat Nfr))))
           (Float.of_int (Int.repr (Z.of_nat Nbg))))
   = Some (Int.repr (Z.of_nat (Ordinal (getBG_col H0 H1 (Ordinal Hk))))).
Proof.
intros.
simpl.
destruct (interpolate_range H0 H1 (Ordinal Hk)).
simpl nat_of_ord in H2,H3.
rewrite (Z2Nat.id k) in H2,H3|-* by rep_lia.
rewrite !Float_of_int_e by rep_lia.
change Float.mul with (@BMULT _ Tdouble).
change Float.div with (@BDIV _ Tdouble).
set (j :=  (Zconst Tdouble k / Zconst Tdouble (Z.of_nat Nfr) * Zconst Tdouble (Z.of_nat Nbg))%F64) in *.
change 1024 with (femax Tdouble).
destruct H3.
pose proof Btrunc_range_pos (Z.of_nat Nbg) j ltac:(rep_lia) ltac:(auto) H2.
rewrite Z2Nat.id by lia.
apply Float_to_int_i; auto.
clear H5.
clearbody j.
split.
apply RIneq.Rle_trans with (Rdefinitions.IZR 0).
apply RIneq.IZR_le. rep_lia.
unfold FT2R.
clear - H2 H3.
-
rewrite BCMP_eq in H3; auto.
destruct (Rle_bool_spec (Binary.B2R (fprec Tdouble) (femax Tdouble) 0%F64) (Binary.B2R (fprec Tdouble) (femax Tdouble) j)); auto; discriminate.
-
destruct (BofZ_exact _ _ (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble) (Z.of_nat Nbg) ltac:(simpl; rep_lia)) as [? [? _]].
unfold Zconst in H4; rewrite (proof_irr (Pos2Z.is_pos (fprecp  Tdouble)) (fprec_gt_0 Tdouble)) in H4.
rewrite BCMP_eq in H4; auto.
unfold FT2R.
destruct (Rle_bool_spec  (Binary.B2R (fprec Tdouble) (femax Tdouble) j)
       (Binary.B2R (fprec Tdouble) (femax Tdouble)
          (BofZ (fprec Tdouble) (femax Tdouble) (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble) Nbg))); try discriminate.
rewrite H5 in H7.
apply RIneq.Rle_trans with (Rdefinitions.IZR (Z.of_nat Nbg)); auto.
apply RIneq.IZR_le. rep_lia.
Qed.

Lemma bg_col_range: 
  forall [Nfr Nbg]
    (H0: 1 < Z.of_nat (S Nfr) <= Int.max_signed)
    (H1: Z.of_nat (S Nbg) <= Int.max_signed)
    k,
  (nat_of_ord (Ordinal (getBG_col H0 H1 k)) <= S Nbg)%nat.
Proof.
intros.
set (H2 := getBG_col _ _ _).
clearbody H2.
simpl in *.
set (u := Z.to_nat _) in *.
lia.
Qed.


Instance InhW : Inhabitant Wave.t := 
  Wave.Build_t O (const_mx (Zconst _ 0))  (const_mx (Zconst _ 0))  (const_mx (Zconst _ 0))  (Zconst _ 0) ltac:(rep_lia).

Instance InhMat (m n: nat) : Inhabitant 'M[ftype Tdouble]_(m,n) := const_mx (Zconst _ 0).

Instance In_ordinal: forall n, Inhabitant (ordinal (S n)) := (fun _ => ord0).

Definition wave_finite (w: Wave.t) :=
 (forall i, Binary.is_finite (Wave.A w ord0 i) && Binary.is_finite (Wave.σ w ord0 i) && Binary.is_finite (Wave.v w ord0 i) = true)%bool /\
 (Binary.is_finite (Wave.θ0 w) = true).
 
Definition MAXW : Z := proj1_sig (opaque_constant 100).
Definition MAXW_eq: MAXW=100 := proj2_sig (opaque_constant 100).
Hint Rewrite MAXW_eq: rep_lia.

Definition updateθ_ [Nfr: nat] (Hfr: 1 < Z.of_nat (S Nfr) <= Int.max_signed) (k: 'I_(S Nfr)) (dt: ftype Tdouble) (θ: ftype Tdouble) (w : Wave.t) : ftype Tdouble :=
  let v := interpolate Hfr (Wave.Hn w) (Wave.v w) (@inord Nfr (ssrnat.subn k 1)) in
   range2pi (@BPLUS _ Tdouble θ (BMULT v dt)).

Definition force_float (v: val) : ftype Tdouble := 
  match v with Vfloat x => x | _ => Zconst _ 0 end.


Section Inside_Synthesize.

  Context
  {Espec : OracleKind} 
  [Nfr Nb Nbg]
  (Hfr : 1 < Z.of_nat (S Nfr) /\ Z.of_nat (S Nb * S Nfr) <= Int.max_signed)
  (Hbg : Z.of_nat (S Nb * S Nbg) <= Int.max_signed)
  (dt : float)
  (BG : 'M[ftype Tdouble]_(S Nb, S Nbg))
  (X : 'M[ftype Tdouble]_(S Nb, S Nfr))
  (Xp Bp  p v_theta: val)
  (wx : list (Wave.t * (val * val * val)))
  (Hwx : Zlength wx <= MAXW)
  (sh : share)
  (SH : readable_share sh).

Definition iteri_upto
  [k: Z]
  (Hk : Datatypes.is_true (ssrnat.leq (S (Z.to_nat k)) (S Nfr)))
  (θw : list (val * Wave.t))
  (energy  diff_sum : ftype Tdouble)
  i := 
  seq.foldl (one_iteri (N_range Hfr) (N_range1 Hfr) (N_range2 Hbg) dt BG X (Ordinal Hk)) (θw, (energy, diff_sum)) (sublist 0 i (ord_enum (S Nb))).

Lemma iteri_upto_Zlength: 
  forall k 
  (Hk : Datatypes.is_true (ssrnat.leq (S (Z.to_nat k)) (S Nfr)))
   θw energy diff_sum i,
      Zlength (fst (iteri_upto Hk θw energy diff_sum i)) = Zlength θw.
Proof.
 intros.
 unfold iteri_upto.
 revert θw energy diff_sum; 
 induction (sublist _ _ _); intros; auto.
 set (f := one_iteri _ _ _ _ _ _ _) in *.
 unfold seq.foldl. fold (seq.foldl f).
 unfold f at 2. unfold one_iteri.
 destruct (eqtype.eq_op _ _); [ | list_solve].
 change @seq.map with @map.
 destruct (eqtype.eq_op _ _). rewrite IHl. list_solve.
 rewrite IHl. list_solve.
Qed.

Lemma iteri_is_float:
  forall k w
  (Hk : Datatypes.is_true (ssrnat.leq (S (Z.to_nat k)) (S Nfr)))
   θw energy diff_sum i
  (H0 : 0 <= i < Z.of_nat (S Nb))
  (Hw: 0 <= w < Zlength θw)
  (Hk0 : k <> 0 -> Forall (is_float oo fst) θw),
      is_float (fst (Znth w (fst (iteri_upto Hk θw energy diff_sum (i+1))))).
Proof.
intros.
pose proof (Zlength_ord_enum (S Nb)).
unfold iteri_upto.
rewrite (sublist_split 0 1 (i+1)) by list_solve.
change @app with @seq.cat. rewrite seq.foldl_cat.
rewrite sublist_len_1 by list_solve.
unfold seq.foldl at 2.
rewrite (@Znth_ord_enum _ _ 0 (ssrnat.ltn0Sn Nb)) by (clear; lia).
set (il := sublist _ _ _). clearbody il.
set (a := one_iteri (N_range Hfr) (N_range1 Hfr) (N_range2 Hbg) dt BG X
                 (Ordinal Hk) (θw, (energy, diff_sum)) _).

assert (Zlength (fst a) = Zlength θw /\  is_float (fst (Znth w (fst a)))).
-
subst a.
unfold one_iteri. 
change @seq.map with @map. 
simpl.
unfold updateθ.
destruct (eqtype.eq_op _ _) eqn:?H.
rewrite ?Znth_map by list_solve.
split. list_solve. simpl. auto.
split. list_solve.
rewrite Znth_map by list_solve.
unfold eqtype.eq_op in H1; simpl in H1. specialize (Hk0 ltac:(lia)).
rewrite Forall_Znth in Hk0. specialize (Hk0 w Hw). destruct (Znth w θw). simpl in Hk0. 
destruct v; try contradiction; auto.  
-
clearbody a.
revert a H1; induction il; simpl; intros; try tauto.
apply IHil.
clear IHil.
unfold one_iteri.
destruct a0 as [t [e d]].
change @seq.map with @map. 
simpl in *.
unfold updateθ.
repeat destruct (eqtype.eq_op _ _);
rewrite ?Znth_map by list_solve; auto.
+ split.
 list_solve. 
simpl. auto.
+ destruct H1. split. list_solve. destruct (Znth w t); auto. simpl in H2.
  destruct v; try contradiction. 
 simpl. auto.
Qed.

Lemma iteri_lemma9: 
 forall (k : Z)
  (H : 0 <= k < S Nfr)
  (Hk : Datatypes.is_true (ssrnat.leq (S (Z.to_nat k)) (S Nfr)))
  (θw : list (val * Wave.t))
  (energy diff_sum : ftype Tdouble)
  (Hk0 : k <> 0 -> Forall (is_float oo fst) θw)
  (i : Z)
  (H0 : 0 < i < S Nb)
  (Hi : Datatypes.is_true (ssrnat.leq (S (Z.to_nat i)) (S Nb)))
  (w : Z)
  (H1 : 0 <= w < Zlength θw),
  fst (Znth w (fst (iteri_upto Hk θw energy diff_sum i))) =
   Vfloat
     (if zeq k 0 then Wave.θ0 (snd (Znth w θw)) else updateθ_ (N_range Hfr) (Ordinal Hk) dt (force_float (fst (Znth w θw))) (snd (Znth w θw))).
Proof.
intros.
unfold updateθ_, iteri_upto.
pose proof (Zlength_ord_enum (S Nb)).
assert (Forall (fun j => 0 < nat_of_ord j) (sublist 1 i (ord_enum (S Nb)))). {
 clear - H2 H0.
 rewrite Forall_Znth; intros.
 rewrite Zlength_sublist in H by lia.
 rewrite Znth_sublist by list_solve.
 assert (Datatypes.is_true (ssrnat.leq (S (Z.to_nat (i0 + 1))) (S Nb))) by lia.
 rewrite (Znth_ord_enum H1) by lia. simpl. lia.
}
rewrite (sublist_split 0 1 i) by list_solve.
rewrite sublist_len_1 by list_solve.
change @app with @seq.cat. rewrite seq.foldl_cat.
unfold seq.foldl at 2.
set (a := one_iteri _ _ _ _ _ _ _) at 1.
unfold one_iteri.
rewrite (@Znth_ord_enum _ _ 0 (ssrnat.ltn0Sn Nb)) by (clear; lia).
destruct (eqtype.eq_op _ _) eqn:H4;
  [ clear H4 | clear - H4; unfold eqtype.eq_op in H4;  simpl in H4; lia].
destruct (eqtype.eq_op _ _) eqn:Hk'.
-
assert (k=0) by (unfold eqtype.eq_op in Hk'; simpl in Hk'; lia).
subst k. rewrite if_true by auto.
set (s := (diff_sum + _)%F64). clearbody s.
set (e := (energy + _)%F64). clearbody e.
subst a.
revert e s; induction H3; intros.
simpl. rewrite Znth_map by list_solve. reflexivity.
simpl seq.foldl.
unfold eqtype.eq_op at 1.
simpl.
unfold eqtype.eq_op at 1.
simpl.
destruct (ssrnat.eqn x _) eqn:?H; [ lia | ].
clear H5.
apply IHForall.
-
rewrite if_false by (unfold eqtype.eq_op in Hk'; simpl in Hk'; lia).
assert (k>0) by (unfold eqtype.eq_op in Hk'; simpl in Hk'; lia).
specialize (Hk0 ltac:(lia)).
set (s := (diff_sum + _)%F64). clearbody s.
set (e := (energy + _)%F64). clearbody e.
subst a.
rewrite Forall_Znth in Hk0. specialize (Hk0 _ H1). red in Hk0.
revert e s; induction H3; intros.
simpl. rewrite Znth_map by list_solve.
unfold updateθ. destruct (Znth w θw) eqn:?H.
simpl fst.
assert (exists θ, v = Vfloat θ). clear - Hk0; destruct v; try contradiction; eauto.
destruct H5 as [θ ?]; subst v.
simpl.
auto.
set (a := one_iteri _ _ _ _ _ _ _) in *.
simpl.
unfold eqtype.eq_op at 1.
simpl.
unfold eqtype.eq_op at 1.
simpl.
destruct (ssrnat.eqn x _) eqn:?H; [ lia | ].
clear H6.
rewrite IHForall.
auto.
Qed.


Lemma semax_synthesize_w_loop:
 forall
  (k : Z)
  (H : 0 <= k < Z.of_nat (S Nfr))
  (Hk : Datatypes.is_true (ssrnat.leq (S (Z.to_nat k)) (S Nfr))),
 let j' := Ordinal (getBG_col (N_range Hfr) (N_range2 Hbg) (Ordinal Hk)) : 'I_(S Nbg) in
 forall (Hbgcol : (nat_of_ord j' <= S Nbg)%nat)
  (θw : list (val * Wave.t))
  (energy  diff_sum : ftype Tdouble)
  (Hθ : map snd θw = map fst wx)
  (Hk0 : k <> 0 -> Forall (is_float oo fst) θw),
 let θw'' := fun i : Z => fst (iteri_upto Hk θw energy diff_sum (i + 1)) in
  forall (i : Z)
  (H0 : 0 <= i < Z.of_nat (S Nb))
  (Hi : Datatypes.is_true (ssrnat.leq (S (Z.to_nat i)) (S Nb)))
  (θw' : list (val * Wave.t))
  (energy' diff_sum' : ftype Tdouble)
  (H1 : iteri_upto Hk θw energy diff_sum i = (θw', (energy', diff_sum'))),
 let i' := Ordinal Hi : 'I_(S Nb) in
 let ew := map (fun f : 'cV_(S Nb) => fun_of_matrix f i' ord0) (map (waveform (N_range Hfr) (N_range1 Hfr) dt (Ordinal Hk)) (θw'' i)) : list (ftype Tdouble) in
  semax (func_tycontext f_synthesize Vprog Gprog nil)
  (PROP ( )
   LOCAL (temp _a (val_of_float (fun_of_matrix BG i' j')); temp _i (Vint (Int.repr i)); temp _bg_col (Vint (Int.repr (Z.of_nat (nat_of_ord j'))));
   temp _k (Vint (Int.repr k)); temp _energy (Vfloat energy'); temp _diff_sum (Vfloat diff_sum'); temp _X Xp; temp _BG Bp;
   temp _waves (field_address tdata (DOT _waves) p); temp _dt (Vfloat dt); temp _Nbg (Vint (Int.repr (Z.of_nat (S Nbg))));
   temp _Nfr (Vint (Int.repr (Z.of_nat (S Nfr)))); temp _Nb (Vint (Int.repr (Z.of_nat (S Nb)))); temp _Nw (Vint (Int.repr (Zlength wx)));
   lvar _theta (tarray tdouble MAXW) v_theta; temp _data p)
   SEP (densematn sh (map_mx Some BG) Bp; 
       data_at sh tdata (Xp, (Bp, (Vint (Int.repr (Z.of_nat (S Nb))), (Vint (Int.repr (Z.of_nat (S Nfr))),
             (Vint (Int.repr (Z.of_nat (S Nbg))), (Vfloat dt, (map wx_to_waverep wx, Vint (Int.repr (Zlength (map fst wx))))))))))
         p;
   data_at Tsh (tarray tdouble MAXW) (map fst θw' ++ Zrepeat Vundef (MAXW - Zlength wx)) v_theta;
   densematn sh (map_mx Some X) Xp; fold_right sepcon emp (map (wx_to_wavedata sh) wx)))
  synthesize_w_loop
 (normal_ret_assert 
  (PROP ( )
   LOCAL (temp _a (Vfloat (seq.foldl BPLUS (BG i' j') ew)); temp _i (Vint (Int.repr i));
   temp _bg_col (Vint (Int.repr (Z.of_nat (nat_of_ord j')))); temp _k (Vint (Int.repr k));
   temp _energy (Vfloat energy'); temp _diff_sum (Vfloat diff_sum'); temp _X Xp; 
   temp _BG Bp; temp _waves (field_address tdata (DOT _waves) p); temp _dt (Vfloat dt);
   temp _Nbg (Vint (Int.repr (Z.of_nat (S Nbg)))); temp _Nfr (Vint (Int.repr (Z.of_nat (S Nfr))));
   temp _Nb (Vint (Int.repr (Z.of_nat (S Nb)))); temp _Nw (Vint (Int.repr (Zlength wx)));
   lvar _theta (tarray tdouble MAXW) v_theta; temp _data p)
   SEP (densematn sh (map_mx Some BG) Bp; 
            data_at sh tdata (Xp, (Bp, (Vint (Int.repr (Z.of_nat (S Nb))), (Vint (Int.repr (Z.of_nat (S Nfr))),
               (Vint (Int.repr (Z.of_nat (S Nbg))), (Vfloat dt, (map wx_to_waverep wx, Vint (Int.repr (Zlength (map fst wx))))))))))
            p;
            data_at Tsh (tarray tdouble MAXW)
                (map fst (θw'' i) ++ Zrepeat Vundef (MAXW - Zlength wx)) v_theta;
            densematn sh (map_mx Some X) Xp;
            fold_right sepcon emp (map (wx_to_wavedata sh) wx)))).
Proof.
intros.
unfold synthesize_w_loop.
forward_for_simple_bound (Zlength wx) (EX w:Z,
   PROP ( )
   LOCAL (temp _a (Vfloat (seq.foldl BPLUS (BG i' j') (sublist 0 w ew))); temp _i (Vint (Int.repr i));
   temp _bg_col (Vint (Int.repr (Z.of_nat (nat_of_ord j')))); temp _k (Vint (Int.repr k));
   temp _energy (Vfloat energy'); temp _diff_sum (Vfloat diff_sum'); temp _X Xp; 
   temp _BG Bp; temp _waves (field_address tdata (DOT _waves) p); temp _dt (Vfloat dt);
   temp _Nbg (Vint (Int.repr (Z.of_nat (S Nbg)))); temp _Nfr (Vint (Int.repr (Z.of_nat (S Nfr))));
   temp _Nb (Vint (Int.repr (Z.of_nat (S Nb)))); temp _Nw (Vint (Int.repr (Zlength wx)));
   lvar _theta (tarray tdouble MAXW) v_theta; temp _data p)
   SEP (densematn sh (map_mx Some BG) Bp;
            data_at sh tdata (Xp, (Bp, (Vint (Int.repr (Z.of_nat (S Nb))), (Vint (Int.repr (Z.of_nat (S Nfr))),
               (Vint (Int.repr (Z.of_nat (S Nbg))), (Vfloat dt, (map wx_to_waverep wx, Vint (Int.repr (Zlength (map fst wx))))))))))
            p;
            data_at Tsh (tarray tdouble MAXW)
                (map fst (sublist 0 w (θw'' i) ++ sublist w (Zlength θw') θw')
                ++ Zrepeat Vundef (MAXW - Zlength wx)) v_theta;
            densematn sh (map_mx Some X) Xp;
            fold_right sepcon emp (map (wx_to_wavedata sh) wx)))%assert.
+ autorewrite with sublist. entailer!!.
+
rename i0 into w.
destruct (Znth w wx) as [[N A σ v θ0]  [[Ap σp] vp]] eqn:?H.
forward; rewrite <- ?MAXW_eq;
  try (rewrite Znth_map by list_solve; rewrite H3; simpl wx_to_waverep); cbv match.
entailer!!. entailer!!.
replace (map (wx_to_wavedata sh) wx)
 with (map (wx_to_wavedata sh) (sublist 0 w wx) ++ [wx_to_wavedata sh (Znth w wx)] ++ 
         map (wx_to_wavedata sh) (sublist (w+1) (Zlength wx) wx)) by list_solve.
rewrite !sepcon_app.
simpl fold_right.
rewrite H3.
simpl wx_to_wavedata.
Intros.
forward; rewrite <- ?MAXW_eq;
  try (rewrite Znth_map by list_solve; rewrite H3; simpl wx_to_waverep); cbv match.
entailer!!. 
entailer!. clear - H20; destruct H20; auto.
cbv match.
pose (Y := existT _ N (Hn,A)  :   {Nt: nat &  ((Z.of_nat (S Nt) <= Int.max_signed) * 'rV[ftype Tdouble]_(S Nt))}).
pose (K := existT _ Nfr (N_range Hfr,(Ordinal Hk)) :  {Nfr & ((1 < Z.of_nat (S Nfr) <= Int.max_signed) * 'I_(S Nfr))}).
forward_call (sh,Y, Ap, K).
simpl firstn.
rewrite Float_of_int_e.  replace (Z.of_nat (Ordinal Hk)) with k by (simpl; lia).
entailer!!.
rep_lia.
clear Y.
forward.
deadvars!.
forward; rewrite <- ?MAXW_eq;
  try (rewrite Znth_map by list_solve; rewrite H3; simpl wx_to_waverep); cbv match.
entailer!!. 
entailer!. clear - H21; destruct H21; auto.
cbv match.
pose (Y := existT _ N (Hn,σ) :  {N:nat & ((Z.of_nat (S N) <= Int.max_signed) * 'rV[ftype Tdouble]_(S N))}).
forward_call (sh,Y, σp, K).
simpl firstn.
rewrite Float_of_int_e.  replace (Z.of_nat (Ordinal Hk)) with k by (simpl; lia).
entailer!!.
rep_lia.
clear Y K.
forward.
assert (forall j, map snd (fst (iteri_upto Hk θw energy diff_sum j)) = map fst wx). {
 intro.
 unfold iteri_upto.
 rewrite <- Hθ.
 forget (sublist 0 j (ord_enum (S Nb))) as L.
 rewrite <- (seq.revK L).
 rewrite seq.foldl_rev.
 induction (seq.rev L); auto.
 set (f := fun _ => _) in IHl|-*. set (ab := (energy, diff_sum)) in IHl|-*.
 unfold seq.foldr; fold (seq.foldr f (θw,ab) l).
 destruct (seq.foldr f _ _) as [? [? ?]].
 rewrite <-IHl.
 clear - Hk0.
 simpl.
 repeat destruct (eqtype.eq_op _ _); simpl;
 change @seq.map with @map; auto.
 rewrite map_map. simpl. f_equal.
 unfold updateθ.
 rewrite map_map. f_equal.
 extensionality xy. destruct xy as [v w].
 destruct v; auto. 
}

assert (Hθ': map snd θw' = map fst wx) by (specialize (H4 i); rewrite H1 in H4; auto).
assert (Hθ'': map snd (θw'' i) = map fst wx). { subst θw''. simpl. specialize (H4 (i+1)). auto. }

deadvars!.
forward_if 
  (PROP ( )
   LOCAL (temp _sigma (Vfloat (interpolate (N_range Hfr) Hn σ (Ordinal Hk)));
    temp _A (Vfloat (interpolate (N_range Hfr) Hn A (Ordinal Hk)));
   temp _Nt (Vint (Int.repr (Z.pos (PosDef.Pos.of_succ_nat N)))); temp _w (Vint (Int.repr w));
   temp _a (Vfloat (seq.foldl BPLUS (fun_of_matrix BG i' j') (sublist 0 w ew))); temp _i (Vint (Int.repr i));
   temp _bg_col (Vint (Int.repr (Z.of_nat (nat_of_ord j')))); temp _k (Vint (Int.repr k));
   temp _energy (Vfloat energy'); temp _diff_sum (Vfloat diff_sum'); temp _X Xp; temp _BG Bp;
   temp _waves (field_address tdata (DOT _waves) p); temp _dt (Vfloat dt);
   temp _Nbg (Vint (Int.repr (Z.of_nat (S Nbg)))); temp _Nfr (Vint (Int.repr (Z.of_nat (S Nfr))));
   temp _Nb (Vint (Int.repr (Z.of_nat (S Nb)))); temp _Nw (Vint (Int.repr (Zlength wx)));
   lvar _theta (tarray tdouble MAXW) v_theta; temp _data p)
   SEP (densematn sh (map_mx Some σ) σp; densematn sh (map_mx Some A) Ap; densematn sh (map_mx Some BG) Bp;
   data_at sh tdata
     (Xp,
      (Bp,
       (Vint (Int.repr (Z.of_nat (S Nb))),
        (Vint (Int.repr (Z.of_nat (S Nfr))),
         (Vint (Int.repr (Z.of_nat (S Nbg))),
          (Vfloat dt, (map wx_to_waverep wx, Vint (Int.repr (Zlength (map fst wx))))))))))
     p;
   data_at Tsh (tarray tdouble MAXW)
         (map fst  (sublist 0 (w+1) (θw'' i) ++ sublist (w+1) (Zlength θw') θw') ++
      Zrepeat Vundef (MAXW - Zlength wx))
     v_theta;
   densematn sh (map_mx Some X) Xp; fold_right sepcon emp (map (wx_to_wavedata sh) (sublist 0 w wx));
   densematn sh (map_mx Some v) vp; emp;
   fold_right sepcon emp (map (wx_to_wavedata sh) (sublist (w + 1) (Zlength wx) wx)))); [ forward_if | | ].
* (* i==0, k==0 *)
subst i k.
forward; rewrite <- ?MAXW_eq;
  try (rewrite Znth_map by list_solve; rewrite H3; simpl wx_to_waverep); cbv match.
entailer!!. entailer!!.
rewrite MAXW_eq.
forward.
entailer!!.
rewrite <- MAXW_eq.
subst θw''.
entailer!!.
apply derives_refl'. f_equal.
rewrite (sublist_split 0 w (w+1)) by list_solve.
rewrite (sublist_split w (w+1) (Zlength θw') θw') by list_solve.
rewrite !sublist_len_1 by list_solve.
replace (Vfloat θ0) with (fst (Znth w (fst (iteri_upto Hk θw energy diff_sum 1)))). 2:{
   unfold iteri_upto.
   pose proof (Zlength_ord_enum (S Nb)).
   rewrite sublist_len_1 by list_solve. simpl.
   replace (eqtype.eq_op _ _) with true.
  change @seq.map with map.
  rewrite Znth_map by list_solve.
  simpl. f_equal. transitivity (Wave.θ0 (Znth w (map fst wx))). rewrite <- Hθ. f_equal. list_solve.
   rewrite Znth_map by list_solve.  rewrite H3. auto.
   rewrite (Znth_ord_enum Hi) by lia.
   unfold eqtype.eq_op; simpl; lia.
}
set (a := Znth w (fst (iteri_upto Hk θw energy diff_sum 1))).
assert (Zlength (fst (iteri_upto Hk θw energy diff_sum 1)) = Zlength wx). 
  rewrite iteri_upto_Zlength. list_solve.
forget (fst (iteri_upto Hk θw energy diff_sum 1)) as b.
clear - H5 Hθ' H2.
rewrite upd_Znth_app1 by list_solve.
rewrite !map_app.
rewrite upd_Znth_app2 by list_solve.
rewrite !Zlength_map.
rewrite Zlength_sublist by list_solve.
  rewrite upd_Znth_app1 by list_solve.
autorewrite with sublist. simpl map.
rewrite upd_Znth0.
rewrite !app_assoc.
auto.
* (* i=0, k != 0 case *)
forward; try (rewrite Znth_map by list_solve; rewrite H3). 
  entailer!!. simpl local. entailer!. destruct H25; auto.
simpl.
pose (Y := existT _ N (Hn,v)  :   {Nt: nat &  ((Z.of_nat (S Nt) <= Int.max_signed) * 'rV[ftype Tdouble]_(S Nt))}).
pose (K := existT _ Nfr (N_range Hfr, (inord (Z.to_nat (k-1)))) :  {Nfr & ((1 < Z.of_nat (S Nfr) <= Int.max_signed) * 'I_(S Nfr))}).
forward_call (sh,Y, vp, K); clear Y K.
entailer!!. simpl. rewrite Float_of_int_e by rep_lia. rewrite inordK by lia. rewrite Z2Nat.id by lia. auto.
forward.
subst i.
forward.
entailer!!.
rewrite Znth_app1 by list_solve. rewrite !Znth_map by list_solve.
rewrite Znth_app2 by list_solve.
rewrite Zlength_sublist by list_solve.
autorewrite with sublist.
rewrite (sublist_split w (w+1)) by list_solve.
rewrite sublist_len_1 by list_solve. simpl.
rewrite Znth_0_cons.
unfold iteri_upto in H1. simpl in H1. inv H1.
clear - Hk0 H6 H2 Hθ'.
apply Hk0 in H6. rewrite Forall_Znth in H6.
apply H6. list_solve.
deadvars!.
rewrite Znth_app1 by list_solve.
rewrite map_app.
rewrite Znth_app2 by list_solve.
rewrite Znth_map by list_solve.
rewrite (sublist_split w (w+1)) by list_solve.
rewrite Znth_app1 by list_solve.
replace (w - _) with 0 by list_solve.
rewrite sublist_len_1 by list_solve.
rewrite Znth_0_cons.
set (vt := interpolate _ _ v _).
generalize H1; unfold iteri_upto at 1. simpl seq.foldl. intros Hx; inv Hx.
assert (is_float (fst (Znth w θw'))). {
 apply Hk0 in H6. rewrite Forall_Znth in H6. apply H6. list_solve.
}
destruct (fst (Znth w θw')) eqn:?H; try contradiction.
change (ftype Tdouble) in f. 
forward_call (BPLUS f (BMULT  vt dt)).
forward.
entailer!!.
apply derives_refl'; f_equal.
rewrite upd_Znth_app1 by list_solve.
rewrite upd_Znth_app2 by list_solve.
autorewrite with sublist.
rewrite Zlength_sublist by list_solve.
autorewrite with sublist.
rewrite map_app.
rewrite upd_Znth_app1 by list_solve.
simpl map.
rewrite upd_Znth0.
f_equal.
unfold θw''.
simpl.
unfold iteri_upto.
replace (sublist 0 1 _) with [@ord0 Nb].
2: clear; compute; destruct ssrbool.idP; try lia; f_equal; apply ord_inj; auto.
simpl.
replace (eqtype.eq_op _ _) with false.
2: unfold eqtype.eq_op; simpl; lia.
change @seq.map with map.
rewrite (sublist_split 0 w (w+1)) by list_solve.
rewrite sublist_len_1 by list_solve.
simpl.
rewrite !sublist_map.
rewrite !map_app.
rewrite !map_map.
rewrite <- !app_assoc.
simpl.
f_equal.
f_equal.
unfold iteri_upto in H1. autorewrite with sublist in H1.   simpl in H1. inv H1.
rewrite Znth_map by list_solve.
unfold updateθ.
destruct (Znth w θw') eqn:?H.
simpl in H7. subst v0. clear H5.
simpl.
f_equal.
f_equal.
replace (interpolate _ _ _ _) with vt. auto.
subst vt.
assert (Znth w (map snd θw') = Znth w (map fst wx)) by list_solve.
rewrite !Znth_map in H5 by list_solve.
rewrite H1,H3 in H5. simpl in H5.
subst t; simpl.
f_equal.
apply ord_inj.
rewrite !inordK; try lia.
*
forward.
entailer!!.
apply derives_refl'; f_equal.
f_equal.
rewrite (sublist_split 0 w (w+1)) by list_solve.
rewrite (sublist_split w (w+1) (Zlength _)) by list_solve.
f_equal.
rewrite !app_assoc.
f_equal.
f_equal.
rewrite !sublist_len_1 by list_solve.
simpl.
f_equal.
unfold θw''.
replace θw' with (fst (iteri_upto Hk θw energy diff_sum i)) by (rewrite H1; auto).
clear - H5 H0.
unfold iteri_upto.
simpl.
pose proof (Zlength_ord_enum (S Nb)).
rewrite (sublist_split 0 i (i+1)) by list_solve.
pose (jj := @ord0 Nb). clearbody jj.
rewrite (@sublist_len_1 _ jj) by list_solve.
rewrite seq.foldl_cat.
destruct (seq.foldl _ _ (sublist _ _ _)) as [? [? ?]].
simpl.
replace (eqtype.eq_op _ _) with false; auto.
unfold eqtype.eq_op; simpl.
erewrite Znth_ord_enum.
simpl. lia. lia.
Unshelve.
lia.
*
forward.
-- entailer!!. rewrite !map_app. rewrite !Znth_app1 by list_solve.
   rewrite (sublist_split 0 w) by list_solve. rewrite Znth_map, Znth_app2, sublist_len_1 by list_solve.
  rewrite Zlength_sublist by list_solve.  autorewrite with sublist.
  subst θw''. cbv beta.
  apply iteri_is_float; auto. list_solve.
--
rewrite !map_app, !Znth_app1 by list_solve.
   rewrite (sublist_split 0 w) by list_solve. rewrite Znth_map, Znth_app2, sublist_len_1 by list_solve.
  rewrite Zlength_sublist by list_solve.  autorewrite with sublist.
 pose (newθ := if zeq k 0 then θ0 else updateθ_ (N_range Hfr) (Ordinal Hk) dt (force_float (fst (Znth w θw))) (fst (Znth w wx))).
  assert (fst (Znth w (θw'' i)) = Vfloat newθ). {
    clear MORE_COMMANDS POSTCONDITION Delta Delta_specs.
    subst newθ θw''. cbv beta.
    unfold iteri_upto.
    pose (Zlength_ord_enum (S Nb)).
    rewrite (sublist_split 0 i (i+1)) by lia.
    change @app with @seq.cat. rewrite seq.foldl_cat.
    fold (iteri_upto Hk θw energy diff_sum i). rewrite H1.
    rewrite sublist_len_1 by lia.
    rewrite (Znth_ord_enum Hi) by lia.
    unfold seq.foldl, one_iteri, fst, eqtype.eq_op; simpl.
    destruct (eqtype.eq_op _ _) eqn:?H; [assert (i=0) by lia | assert (i>0) by lia].
    - subst i.
     set (u := eqtype.eq_op _ _).
    destruct u eqn:?H; subst u; [assert (k=0) by rep_lia | assert (k>0) by lia].
    +
    subst k. rewrite if_true by auto. rewrite Znth_map by list_solve.
    f_equal.
    clear - Hθ' H3 H2. 
    transitivity (Wave.θ0 (Znth w (map snd θw'))). f_equal. list_solve.
    rewrite Hθ'. rewrite Znth_map by list_solve. rewrite H3.  simpl. auto.
   +
    change @seq.map with @map.
    rewrite if_false by lia.
    rewrite Znth_map by list_solve. unfold updateθ, updateθ_.
    rewrite H3. simpl.
    change (force_float _) with (force_float (fst (Znth w θw))).
    assert(fst (Znth w θw') = fst (Znth w θw)). { 
       clear - H1 H2 H7.
       unfold iteri_upto. simpl in H1. inv H1. auto.
    }
    rewrite <-H8.
    destruct (Znth w θw') as [v' w'] eqn:?H. simpl in H8. subst v'.
    simpl fst.
    assert (w' = fst (Znth w wx)). transitivity (Znth w (map fst wx)). rewrite <- Hθ'. rewrite Znth_map by list_solve. rewrite H9; auto. list_solve.
    subst w'.
    rewrite H3. simpl.
    set (y := interpolate _ _ _ _). clearbody y.
    unfold iteri_upto in H1. simpl in H1. inv H1.
    spec Hk0; [ lia |].
    rewrite Forall_Znth in Hk0. specialize (Hk0 w ltac:(list_solve)).
    hnf in Hk0. destruct (fst (Znth w θw')); try contradiction; auto.
  - 
   clear H5.
   fold (fst (Znth w θw')). fold (fst (Znth w wx)). fold (fst (Znth w θw)).
   replace θw' with (fst ( iteri_upto Hk θw energy diff_sum i )) by (rewrite H1; auto).
   replace θ0 with (Wave.θ0 (fst (Znth w wx))) by (rewrite H3; auto).
   replace (fst (Znth w wx)) with (snd (Znth w θw)) by (clear - Hθ H2;  list_solve).
   apply iteri_lemma9; auto; try list_solve.
 }
 rewrite H5.
  pose (iLBθ := BMINUS
                (BMULT (Zconst Tdouble i)
                         (BDIV (@BMULT _ Tdouble (Float.of_bits (Int64.repr 4611686018427387904))
                                      (Float.of_bits (Int64.repr 4614256656552045848)))
                            (Zconst _ (Z.of_nat (S Nb)))))
               newθ).
  forward_call iLBθ.
 ++
  simpl firstn. entailer!!. f_equal. f_equal. 
  prove_float_exprs_equal.
 ++
 forward.
 pose (σ' := interpolate (N_range Hfr) Hn σ (Ordinal Hk)).
 pose (exparg := BOPP (BDIV (BMULT (wrap iLBθ) (wrap (iLBθ))) (BMULT (Zconst _ 2) (BMULT σ' σ')))).
 freeze FR1 := - .
 forward_call exparg. simpl firstn.
 apply prop_right.  f_equal. f_equal.
 prove_float_exprs_equal.
 forward.
 rewrite !Zlength_map.
 entailer!!.
 f_equal.
 assert (Zlength ew = Zlength wx) by (subst ew; list_solve).
 rewrite (sublist_split 0 w (w+1)) by list_solve.
 change @app with @seq.cat. rewrite seq.foldl_cat.
 set (firstpart := seq.foldl _ _ (sublist 0 w _)).
 rewrite sublist_len_1 by list_solve. simpl.
 change Float.add with (@BPLUS _ Tdouble).
 apply f_equal2; auto.
 subst ew.

 rewrite !Znth_map by list_solve.
  unfold waveform. destruct (Znth w (θw'' i)) as [vw ww] eqn:?H. simpl in H5. subst vw.
  rewrite mxE. 
 change Float.mul with (@BMULT _ Tdouble).
 assert (ww = fst (Znth w wx)). { transitivity (Znth w (map snd (θw'' i))). rewrite Znth_map, H7; auto; list_solve.
      rewrite Hθ'', Znth_map; list_solve.
 }
 subst ww.
 rewrite H3. simpl Wave.A. simpl Wave.N.
 subst exparg iLBθ. simpl Wave.σ.
 simpl nat_of_ord. rewrite Z2Nat.id by lia. unfold L, M_PI.
 prove_float_exprs_equal.
 thaw FR1.
 match goal with |- ?A |-- ?B =>
   match A with context [data_at _ _ ?A' v_theta] =>
    match B with context [data_at _ _ ?B' v_theta] => replace B' with A' 
  end  end end.
 cancel.
 2:{ rewrite (sublist_split 0 w (w+1)) by list_solve. rewrite sublist_len_1 by list_solve. rewrite <- !map_app.
 rewrite <- app_assoc. f_equal.
 }
 apply derives_trans with (fold_right sepcon emp (map (wx_to_wavedata sh) (sublist 0 w wx)) *
      fold_right sepcon emp (map (wx_to_wavedata sh) (sublist w (w+1) wx)) *
      fold_right sepcon emp (map (wx_to_wavedata sh) (sublist (w+1) (Zlength wx) wx))).
  cancel.
 rewrite sublist_len_1 by list_solve. simpl. unfold wx_to_wavedata.
 rewrite H3. simpl. cancel.
 rewrite <-!sepcon_app.
 apply derives_refl'. f_equal.
 rewrite <-!map_app. f_equal.
 list_solve.
+

assert (Zlength (θw'' i) = Zlength wx)
  by (subst θw''; cbv beta; rewrite iteri_upto_Zlength; list_solve).
assert (Zlength θw' = Zlength wx). {
  replace θw' with (fst (iteri_upto Hk θw energy diff_sum i)) by (rewrite H1; auto).
  rewrite iteri_upto_Zlength; list_solve.
}
entailer!!.
f_equal. f_equal. subst ew.
rewrite map_map, sublist_map.
f_equal.
list_solve.
apply derives_refl'; f_equal.
list_solve.
Qed.

Lemma iterk_defined_θ: forall
 (k : Z)
 (H : 0 <= k < S Nfr)
 (θed : list (val * Wave.t) * (ftype Tdouble * ftype Tdouble))
 (H1 : k <> 0),
Forall (is_float oo fst)
  (fst
     (seq.foldl (one_iterk (N_range Hfr) (N_range1 Hfr) (N_range2 Hbg) dt BG X) θed
        (firstn (Z.to_nat k) (ord_enum (S Nfr))))).
Proof.
intros.
pose proof (Zlength_ord_enum (S Nfr)).
rewrite <- sublist_firstn.
rewrite (sublist_split 0 1 k)  by list_solve.
change @app with @seq.cat; rewrite seq.foldl_cat.
rewrite sublist_len_1 by list_solve.
unfold seq.foldl at 2.
rewrite (@Znth_ord_enum _ _ 0 (ssrnat.ltn0Sn Nfr)) by (clear; lia).
replace (Ordinal _) with (@ord0 Nfr) by (apply ord_inj; reflexivity).
set (al := sublist _ _ _); clearbody al.
set (u := one_iterk _ _ _ _ _ _ _ ord0).
assert (Forall (is_float oo fst) (fst u)).
-
subst u.
destruct θed as [θ [e d]].
simpl.
change @seq.map with @map.
apply Forall_map.
apply Forall_Znth; intros; hnf; auto.
-
clearbody u.
clear k H H1.
revert u H2.
induction al; intros; auto.
simpl.
apply IHal; clear IHal.
clear - H2.
destruct u as [θ [e d]].
simpl.
change @seq.map with @map.
destruct (eqtype.eq_op _ _); apply Forall_map.
apply Forall_Znth; intros; hnf; auto.
unfold updateθ.
simpl in H2.
induction H2; constructor; auto.
hnf.
red in H.
destruct x.
destruct v; try contradiction. simpl; auto.
Qed.

Lemma semax_synthesize_i_loop:
 forall (k: Z) 
 (H : 0 <= k < Z.of_nat (S Nfr))
 (Hk : Datatypes.is_true (ssrnat.leq (S (Z.to_nat k)) (S Nfr))),
semax (func_tycontext f_synthesize Vprog Gprog nil)
  (PROP ( )
   LOCAL (
    temp _bg_col (Vint (Int.repr (Z.of_nat (nat_of_ord (Ordinal (getBG_col (N_range Hfr) (N_range2 Hbg)  (Ordinal Hk) ))))));
   temp _k (Vint (Int.repr k));
   temp _energy (Vfloat (fst (snd (iterk (N_range Hfr) (N_range1 Hfr) (N_range2 Hbg) dt BG X (map fst wx) (Z.to_nat k)))));
   temp _diff_sum (Vfloat (snd (snd (iterk (N_range Hfr) (N_range1 Hfr) (N_range2 Hbg)  dt BG X (map fst wx) (Z.to_nat k))))); 
   temp _X Xp; temp _BG Bp; temp _waves (field_address tdata (DOT _waves) p); temp _dt (Vfloat dt);
   temp _Nbg (Vint (Int.repr (S Nbg))); temp _Nfr (Vint (Int.repr (S Nfr)));
   temp _Nb (Vint (Int.repr (S Nb))); temp _Nw (Vint (Int.repr (Zlength (map fst wx))));
   lvar _theta (tarray tdouble  MAXW) v_theta; temp _data p)
   SEP (data_at sh tdata (Xp, (Bp, (Vint (Int.repr (Z.of_nat (S Nb))), (Vint (Int.repr (Z.of_nat (S Nfr))),
               (Vint (Int.repr (Z.of_nat (S Nbg))), (Vfloat dt, (map wx_to_waverep wx, Vint (Int.repr (Zlength (map fst wx))))))))))
            p;
   data_at Tsh (tarray tdouble MAXW)
       (map fst (fst (iterk (N_range Hfr)(N_range1 Hfr)  (N_range2 Hbg)  dt BG X (map fst wx) (Z.to_nat k))) ++
      Zrepeat Vundef (MAXW - Zlength wx))
     v_theta;
   densematn sh (map_mx Some X) Xp; densematn sh (map_mx Some BG) Bp;
   fold_right sepcon emp (map (wx_to_wavedata sh) wx)))
  synthesize_i_loop
  (normal_ret_assert
     (PROP ( )
      LOCAL (
       temp _k (Vint (Int.repr k));
       temp _energy (Vfloat (fst (snd (iterk (N_range Hfr)(N_range1 Hfr)  (N_range2 Hbg) dt BG X (map fst wx) (Z.to_nat (k + 1))))));
       temp _diff_sum (Vfloat (snd (snd (iterk (N_range Hfr) (N_range1 Hfr) (N_range2 Hbg) dt BG X (map fst wx) (Z.to_nat (k + 1)))))); 
       temp _X Xp; temp _BG Bp; temp _waves (field_address tdata (DOT _waves) p); temp _dt (Vfloat dt);
       temp _Nbg (Vint (Int.repr (S Nbg))); temp _Nfr (Vint (Int.repr (S Nfr)));
       temp _Nb (Vint (Int.repr (S Nb))); temp _Nw (Vint (Int.repr (Zlength (map fst wx))));
       lvar _theta (tarray tdouble MAXW) v_theta; temp _data p)
      SEP (data_at sh tdata (Xp, (Bp, (Vint (Int.repr (Z.of_nat (S Nb))), (Vint (Int.repr (Z.of_nat (S Nfr))),
               (Vint (Int.repr (Z.of_nat (S Nbg))), (Vfloat dt, (map wx_to_waverep wx, Vint (Int.repr (Zlength (map fst wx))))))))))
            p;
      data_at Tsh (tarray tdouble MAXW)
        (map fst (fst (iterk (N_range Hfr) (N_range1 Hfr) (N_range2 Hbg) dt BG X (map fst wx) (Z.to_nat (k + 1)))) ++
         Zrepeat Vundef (MAXW - Zlength wx))
        v_theta;
      densematn sh (map_mx Some X) Xp; densematn sh (map_mx Some BG) Bp;
      fold_right sepcon emp (map (wx_to_wavedata sh) wx)))).
Proof.
intros.
rewrite Zlength_map.
assert (Hbgcol :=bg_col_range (N_range Hfr) (N_range2 Hbg)  (Ordinal Hk)).
unfold iterk.
replace (Z.to_nat (k+1)) with (Z.to_nat k + 1)%nat by lia.
rewrite <- firstn_app.
change (@app ('I_(S Nfr))) with (@seq.cat ('I_(S Nfr))).
rewrite seq.foldl_cat.
set (u := seq.foldl _ _ (firstn (Z.to_nat k) (ord_enum (S Nfr)))).
assert (Hθ: map snd (fst u) = map fst wx). {
 forget (firstn (Z.to_nat k) (ord_enum (S Nfr))) as L.
 clear; subst u.
 unfold initial_values.
 change @seq.map with @map.
 rewrite map_map.
 rewrite <- (seq.revK L). rewrite seq.foldl_rev.
 induction (seq.rev L); simpl.
 rewrite !map_map. simpl. f_equal. rewrite <- IHl; clear IHl.
 destruct (seq.foldr _ _ _). simpl in *. destruct p; simpl.
 destruct (eqtype.eq_op _ _);
 rewrite !map_map; f_equal.
 extensionality x. destruct x,v; simpl; auto.
}
destruct u as [θw [energy diff_sum]] eqn:?H.
assert (Hk0: k <> 0 -> Forall (is_float oo fst) θw). {
 intro.
 replace θw with (fst u) by (rewrite H0; auto).
 subst u.
 apply iterk_defined_θ; auto.
}
clearbody u. clear H0 u. 
simpl in Hθ.
replace (firstn 1 (skipn (Z.to_nat k) (ord_enum (S Nfr)))) with [@Znth _ ord0 k (ord_enum (S Nfr))].
2:{
change 1%nat with (Z.to_nat 1).
rewrite <- sublist_firstn.
rewrite <- sublist_skip by lia.
assert (Zlength (ord_enum (S Nfr)) = Z.of_nat (S Nfr)).
rewrite Zlength_correct, mv_mathcomp.size_ord_enum; auto.
autorewrite with sublist.
symmetry; apply sublist_one; try lia.
}
change (seq.foldl ?A ?B [?C]) with (A B C).
rewrite (Znth_ord_enum Hk) by lia; auto.
change (snd (?A,?B)) with B.
repeat change (fst (?A,?B)) with A.
rewrite <- all_iteri.
unfold synthesize_i_loop.
abbreviate_semax.
set (iteri_upto i := seq.foldl (one_iteri (N_range Hfr) (N_range1 Hfr) (N_range2 Hbg) dt BG X (Ordinal Hk)) (θw, (energy, diff_sum)) (sublist 0 i (ord_enum (S Nb)))).
set (θw'' i := fst (iteri_upto (i+1))).
forward_for_simple_bound (Z.of_nat (S Nb)) (EX i:Z,
     (PROP ( )
      LOCAL (
       temp _bg_col (Vint (Int.repr (Z.of_nat (nat_of_ord (Ordinal (getBG_col  (N_range Hfr) (N_range2 Hbg) (Ordinal Hk)))))));
      temp _k (Vint (Int.repr k));
      temp _energy
        (Vfloat (fst (snd (iteri_upto i))));
      temp _diff_sum (Vfloat (snd (snd (iteri_upto i))));
      temp _X Xp; temp _BG Bp; temp _waves (field_address tdata (DOT _waves) p); temp _dt (Vfloat dt);
      temp _Nbg (Vint (Int.repr (Z.of_nat (S Nbg)))); temp _Nfr (Vint (Int.repr (Z.of_nat (S Nfr))));
      temp _Nb (Vint (Int.repr (Z.of_nat (S Nb)))); temp _Nw (Vint (Int.repr (Zlength wx)));
      lvar _theta (tarray tdouble MAXW) v_theta; temp _data p)
      SEP (data_at sh tdata (Xp, (Bp, (Vint (Int.repr (Z.of_nat (S Nb))), (Vint (Int.repr (Z.of_nat (S Nfr))),
               (Vint (Int.repr (Z.of_nat (S Nbg))), (Vfloat dt, (map wx_to_waverep wx, Vint (Int.repr (Zlength (map fst wx))))))))))
            p;
      data_at Tsh (tarray tdouble MAXW)
        (map fst (fst (iteri_upto i)) ++ Zrepeat Vundef (MAXW - Zlength wx))
        v_theta;
      densematn sh (map_mx Some X) Xp; densematn sh (map_mx Some BG) Bp;
      fold_right sepcon emp (map (wx_to_wavedata sh) wx))))%assert.
- autorewrite with sublist. simpl seq.foldl. entailer!!.
-
set (j' := Ordinal  (getBG_col (N_range Hfr) (N_range2 Hbg) (Ordinal Hk) )) in *.
assert (Hi: Datatypes.is_true (ssrnat.leq (S (Z.to_nat i)) (S (Nb)))) by lia.
set (i' := Ordinal Hi).
forward_densematn_get (map_mx Some BG) i' j' Bp sh (BG i' j').
 entailer!!. simpl. rewrite (Z2Nat.id i) by lia. rewrite (Z2Nat.id k) by lia. rewrite Z2Nat.id; auto.
pose proof (bg_col_is Nbg H (N_range Hfr) (N_range2 Hbg) Hk). fold j' in H1.
apply Float_to_int_e in H1.
change Float.div with (@BDIV _ Tdouble) in H1.
change Float.mul with (@BMULT _ Tdouble) in H1.
rewrite !Float_of_int_e in H1 by rep_lia.
rewrite Int.signed_repr in H1 by rep_lia.
change (fprec Tdouble) with 53.
rewrite (Binary_Btrunc_Zoffloat _ _ H1). lia.
unfold map_mx; rewrite mxE; auto.
destruct (iteri_upto i) as [θw' [energy'  diff_sum']] eqn:?H.
simpl fst; simpl snd.
set (ew := map (fun f: matrix (ftype Tdouble) (S Nb) 1%nat => fun_of_matrix f i' ord0) (map (waveform (N_range Hfr) (N_range1 Hfr) dt (Ordinal Hk)) (θw'' i))).
eapply semax_seq.
+
apply semax_synthesize_w_loop; auto.
unfold nat_of_ord.
simpl.
assumption.
rewrite <- H1; reflexivity.
+
abbreviate_semax.
forward_densematn_get (map_mx Some X) i' (Ordinal Hk) Xp sh (X i' (Ordinal Hk)).
simpl firstn. entailer!!. repeat f_equal; simpl; lia.
unfold map_mx; rewrite mxE; auto.
forward_call.
forward.
forward_call.
forward.
entailer!!.
change (Inside_Synthesize.iteri_upto Hk θw energy diff_sum) with iteri_upto.
change (Binary.Babs _ _ _) with (@BABS _ Tdouble).
change Float.add with (@BPLUS _ Tdouble).
change (Ordinal (getBG_col _ _ _)) with j'.
change Float.sub with (@BMINUS _ Tdouble).
change (map _ (map _ _)) with ew.
subst ew θw''. cbv beta.
unfold iteri_upto.
pose proof (Zlength_ord_enum (S Nb)).
rewrite (sublist_split 0 i) by list_solve.
change @app with @seq.cat; rewrite seq.foldl_cat.
fold (iteri_upto i).
rewrite H1.
rewrite sublist_len_1 by list_solve.
unfold seq.foldl at 1 2.
rewrite (Znth_ord_enum Hi) by lia.
clear H1.
unfold one_iteri.
simpl.
split; f_equal; f_equal.
-
unfold iteri_upto.
pose proof (Zlength_ord_enum (S Nb)).
rewrite (sublist_same 0 (Z.of_nat (S Nb))) by list_solve.
rewrite Zlength_map.
entailer!!.
Qed.

End Inside_Synthesize.

Lemma body_synthesize: semax_body Vprog Gprog f_synthesize synthesize_spec.
Proof.
start_function.
rewrite <- MAXW_eq.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
entailer!. destruct H10; auto.  (* why is this needed? *)
forward.
entailer!. destruct H7; auto.
forward.
forward.
simpl offset_val.
assert_PROP (field_compatible tdata (DOT _waves) p) as Hp by entailer!.
replace (offset_val 40 p) with (field_address tdata (DOT _waves) p) by (rewrite field_address_offset; auto).
destruct d. simpl in H; simpl. subst waves.
assert (Hfr': Z.of_nat (S Nb * S Nfr) <= Int.max_signed) by (destruct Hfr; rewrite <- ssrnat.mulnE; auto).
assert (Hbg': Z.of_nat (S Nb * S Nbg) <= Int.max_signed) by (rewrite <- ssrnat.mulnE; auto).
assert_PROP (Zlength wx <= MAXW) as H1. {
  entailer!.
 simplify_value_fits in H2.
 decompose [and] H2; clear H2. simplify_value_fits in H16.
 rewrite <- MAXW_eq in H16.
 destruct H16. clear - H2. list_solve.
}
freeze FR1 := (data_at _ tdata _ p).
change (Float.of_bits (Int64.repr 0)) with (Zconst Tdouble 0).
forward_for_simple_bound (Z.of_nat (S Nfr)) 
  (EX k:Z, 
   PROP()
   LOCAL (temp _energy (Vfloat (fst (snd (iterk (N_range Hfr) (N_range1 Hfr) (N_range2 Hbg) dt BG X (map fst wx) (Z.to_nat k)))));
   temp _diff_sum (Vfloat (snd (snd (iterk (N_range Hfr)  (N_range1 Hfr) (N_range2 Hbg) dt BG X (map fst wx) (Z.to_nat k)))));
   temp _X Xp; temp _BG Bp; temp _waves (field_address tdata (DOT _waves) p); temp _dt (Vfloat dt);
   temp _Nbg (Vint (Int.repr (S Nbg))); temp _Nfr (Vint (Int.repr (S Nfr)));
   temp _Nb (Vint (Int.repr (S Nb))); temp _Nw (Vint (Int.repr (Zlength (map fst wx))));
   lvar _theta (tarray tdouble MAXW) v_theta; temp _data p)
   SEP (FRZL FR1; 
   data_at Tsh (tarray tdouble MAXW) 
       (map fst (fst (iterk (N_range Hfr) (N_range1 Hfr)  (N_range2 Hbg) dt BG X (map fst wx) (Z.to_nat k))) ++ Zrepeat Vundef (MAXW-Zlength wx)) v_theta; 
   densematn sh (map_mx Some X) Xp;
   densematn sh (map_mx Some BG) Bp;
   fold_right sepcon emp (map (wx_to_wavedata sh) wx)))%assert.
- 
  unfold iterk. simpl firstn. unfold seq.foldl. simpl fst. simpl snd.
  entailer!!.
  apply data_at__data_at. change @seq.map with @map. rewrite !map_map. simpl.
  transitivity (Zrepeat Vundef (Zlength wx) ++ Zrepeat Vundef (MAXW-Zlength wx)).
  f_equal.
  induction wx; auto. rewrite Zlength_cons. unfold Z.succ. rewrite Z.add_comm. rewrite <-Zrepeat_app by rep_lia.
  simpl. f_equal; auto. apply IHwx.  list_solve.
  unfold default_val; simpl. list_solve.
-
rename i into k.
assert (Hk := mk_ord H).
pose proof (bg_col_is Nbg H (N_range Hfr) (N_range2 Hbg) Hk).
forward.
entailer!!.
repeat change (Z.pos (PosDef.Pos.of_succ_nat ?A)) with (Z.of_nat (S A)).
rewrite !inj_S. unfold Z.succ. rewrite !Z.add_simpl_r.
rewrite (Float_to_int_e _ _ H0).
entailer!!.
replace (force_val _) with (Vint (Int.repr (Z.of_nat (Ordinal (getBG_col (N_range Hfr) (N_range2 Hbg) (Ordinal Hk)  ))))).
2:{
simpl force_val.
rewrite !sub_repr.
unfold sem_cast, classify_cast, tint, tdouble, sem_cast_f2i, cast_float_int, cast_int_int.
repeat change (Z.pos (PosDef.Pos.of_succ_nat ?A)) with (Z.of_nat (S A)).
rewrite !inj_S. unfold Z.succ. rewrite !Z.add_simpl_r.
rewrite H0. reflexivity.
}
clear H0.
subst POSTCONDITION; unfold abbreviate.
thaw FR1.
apply semax_synthesize_i_loop; auto.
-
 thaw FR1.
 forward.
 unfold synth_err. 
 set (d := Data.Build_t _ _ _ _ _ _ _).
 rewrite !Nat2Z.id.
 set (u := iterk _ _ _ _ _). clearbody u; destruct u as [? [? ?]].
 simpl. 
 rewrite prop_true_andp by auto.
 set (foo := _ ++ _). clearbody foo.
 unfold data_rep.
 Exists Xp Bp wx. simpl.
 rewrite <- MAXW_eq.
 entailer!!.
Qed.

