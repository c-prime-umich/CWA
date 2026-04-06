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

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition Gprog := [ densematn_get_spec; floor_spec; exp_spec; range2pi_spec; wrap_spec; interpolate_spec; synthesize_spec].

Ltac equal_float_constants :=
lazymatch goal with |- @eq ?t ?A ?B =>
  let t' := eval hnf in t in 
  lazymatch t' with Binary.binary_float _ _ => idtac 
  | _ => fail "Ltac equal_float_constants works only on equalities of type binary_float, instead got" t
  end;
  with_strategy transparent [Float.of_bits]
      (let a := eval hnf in A in let b := eval hnf in B in change (a=b));
   try solve [f_equal; apply proof_irr];
   fail "Ltac equal_float_constants found seemingly unequal values" A "and" B
 | |- _ => fail "Ltac equal_float_constants works only on equalities of type binary_float"
end.

Ltac prove_float_exprs_equal := 
repeat first [ reflexivity
                   | apply (f_equal2 (@BPLUS nans Tdouble))
                   | apply (f_equal2 (@BMINUS nans Tdouble))
                   | apply (f_equal2 (@BMULT nans Tdouble))
                   | apply (f_equal2 (@BDIV nans Tdouble))
                   | apply (f_equal (@BOPP nans Tdouble))
                   | equal_float_constants 
                  ].

Lemma body_range2pi: semax_body Vprog Gprog f_range2pi range2pi_spec.
Proof.
start_function.
forward_call.
forward.
entailer!!.
f_equal.
prove_float_exprs_equal.
Qed.

Lemma body_wrap: semax_body Vprog Gprog f_wrap wrap_spec.
Proof.
start_function.
forward_call.
forward.
entailer!!.
f_equal.
with_strategy opaque [range2pi] prove_float_exprs_equal.
f_equal.
prove_float_exprs_equal.
Qed.

(*
Definition iterk_upto [Nfr Nb Nbg : nat]  (dt: ftype Tdouble) (BG :  'M[ftype Tdouble]_(S Nb,S Nbg)) 
          (X:  'M[ftype Tdouble]_(S Nb, S Nfr)) (k: Z)
         (waves: list Wave.t) : (ftype Tdouble * ftype Tdouble) := 
  iterk dt BG X (Z.to_nat k) (seq.zip (map Wave.θ0 waves) waves) (Zconst _ 0) (Zconst _ 0).

Lemma iterk_upto_end: forall [Nfr Nb Nbg] dt (BG: 'M_(S Nb, S Nbg)) (X: 'M_(S Nb, S Nfr)) waves,
    iterk_upto dt BG X (Z.of_nat (S Nfr)) waves = iterk dt BG X (S Nfr) (seq.zip (seq.map Wave.θ0 waves) waves) (Zconst _ 0) (Zconst _ 0).
Proof.
intros.
unfold iterk_upto.
f_equal.
lia.
Qed.
 
Definition θ_upto (Nfr: nat) (dt: ftype Tdouble) (k: 'I_(S Nfr))  (w: Wave.t) : val :=
 if zeq k 0 
 then Vundef
 else Vfloat (fold_left (fun θ i => fst (updateθ i dt (θ,w))) (firstn (S k) (ord_enum (S Nfr))) (Wave.θ0 w)).
*)

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

Lemma bg_col_is: forall [Nfr k] Nbg 
    (H: 0 <= k < Z.of_nat (S Nfr))
    (Hk: Datatypes.is_true (ssrnat.leq (S (Z.to_nat k)) (S Nfr))),
     Float.to_int
        (Float.mul
           (Float.div (Float.of_int (Int.repr k))
              (Float.of_int (Int.repr (Z.of_nat Nfr))))
           (Float.of_int (Int.repr (Z.of_nat Nbg))))
   = Some (Int.repr (Z.of_nat (Ordinal (getBG_col Nfr Nbg (Ordinal Hk))))).
Admitted.

Lemma bg_col_range: 
  forall Nfr Nbg k, (nat_of_ord (Ordinal (getBG_col Nfr Nbg k)) <= S Nfr)%nat.
Admitted.

Lemma Float_to_int_e: forall x i, Float.to_int x = Some i -> Zoffloat x = Some (Int.signed i).
Admitted.

Lemma Float_of_int_e: forall k,
  Int.min_signed <= k <= Int.max_signed ->
  Float.of_int (Int.repr k) = Zconst Tdouble k.
Admitted.

Lemma Binary_Btrunc_Zoffloat: forall x i, Zoffloat x = Some i -> Binary.Btrunc _ _ x = i.
Admitted.

Instance InhW : Inhabitant Wave.t.
red. econstructor. instantiate (1:=O). 
apply (const_mx (Zconst _ 0)).
apply (const_mx (Zconst _ 0)).
apply (const_mx (Zconst _ 0)).
apply (Zconst _ 0).
Qed.

Instance In_ordinal: forall n, Inhabitant (ordinal (S n)) := (fun _ => ord0).

Definition wave_finite (w: Wave.t) :=
 (forall i, Binary.is_finite (Wave.A w ord0 i) && Binary.is_finite (Wave.σ w ord0 i) && Binary.is_finite (Wave.v w ord0 i) = true)%bool /\
 (Binary.is_finite (Wave.θ0 w) = true).
 
Definition MAXW : Z := proj1_sig (opaque_constant 100).
Definition MAXW_eq: MAXW=100 := proj2_sig (opaque_constant 100).
Hint Rewrite MAXW_eq: rep_lia.


Lemma semax_synthesize_w_loop:
forall {Espec : OracleKind} [Nfr Nb Nbg : nat]
 (dt : float) (BG : 'M[ftype Tdouble]_(S Nb, S Nbg)) (X : 'M[ftype Tdouble]_(S Nb, S Nfr))
 (Xp Bp p v_theta : val)
 (sh : share)
  (k : Z)
  (wx : list (Wave.t * (val * val * val)))
  (SH : readable_share sh)
  (Hfr : Z.of_nat (S Nb * S Nfr) <= Int.max_signed)
  (Hbg : Z.of_nat (S Nb * S Nbg) <= Int.max_signed)
  (Hwx : Zlength wx <= MAXW)
  (H : 0 <= k < Z.of_nat (S Nfr))
  (Hk : Datatypes.is_true (ssrnat.leq (S (Z.to_nat k)) (S Nfr))),
let FR1 := @abbreviate _ 
  (map
    (fun i : nat =>
     freezer.my_nth i
       [data_at_ Tsh (tarray tdouble MAXW) v_theta;
        data_at sh tdata
          (Xp,
           (Bp,
            (Vint (Int.repr (Z.of_nat (S Nb))),
             (Vint (Int.repr (Z.of_nat (S Nfr))),
              (Vint (Int.repr (Z.of_nat (S Nbg))),
               (Vfloat dt, (map wx_to_waverep wx, Vint (Int.repr (Zlength (map fst wx))))))))))
          p;
        densematn sh (map_mx Some X) Xp;
        densematn sh (map_mx Some BG) Bp;
        fold_right sepcon emp (map (wx_to_wavedata sh) wx)]
       emp)
    (map Z.to_nat [1])) in  
 let j' := Ordinal (getBG_col Nfr Nbg (Ordinal Hk)) : 'I_(S Nbg) in
 forall (Hbgcol : (nat_of_ord j' <= S Nfr)%nat)
  (θw : list (val * Wave.t))
  (energy  diff_sum : ftype Tdouble)
  (Hθ : map snd θw = map fst wx)
  (Hk0 : k <> 0 -> Forall (is_float oo fst) θw),
 let iteri_upto :=
  fun i : Z => seq.foldl (one_iteri dt BG X (Ordinal Hk)) (θw, (energy, diff_sum)) (sublist 0 i (ord_enum (S Nb))) in
 let θw'' := fun i : Z => fst (iteri_upto (i + 1)) in
  forall (i : Z)
  (H0 : 0 <= i < Z.of_nat (S Nb))
  (Hi : Datatypes.is_true (ssrnat.leq (S (Z.to_nat i)) (S Nb)))
  (θw' : list (val * Wave.t))
  (energy' diff_sum' : ftype Tdouble)
  (H1 : iteri_upto i = (θw', (energy', diff_sum'))),
 let i' := Ordinal Hi : 'I_(S Nb) in
 let ew := map (fun f : 'cV_(S Nb) => fun_of_matrix f i' ord0) (map (waveform dt (Ordinal Hk)) (θw'' i)) : list (ftype Tdouble) in
  semax (func_tycontext f_synthesize Vprog Gprog nil)
  (PROP ( )
   LOCAL (temp _a (val_of_float (fun_of_matrix BG i' j')); temp _i (Vint (Int.repr i)); temp _bg_col (Vint (Int.repr (Z.of_nat (nat_of_ord j'))));
   temp _k (Vint (Int.repr k)); temp _energy (Vfloat energy'); temp _diff_sum (Vfloat diff_sum'); temp _X Xp; temp _BG Bp;
   temp _waves (field_address tdata (DOT _waves) p); temp _dt (Vfloat dt); temp _Nbg (Vint (Int.repr (Z.of_nat (S Nbg))));
   temp _Nfr (Vint (Int.repr (Z.of_nat (S Nfr)))); temp _Nb (Vint (Int.repr (Z.of_nat (S Nb)))); temp _Nw (Vint (Int.repr (Zlength wx)));
   lvar _theta (tarray tdouble MAXW) v_theta; temp _data p)
   SEP (densematn sh (map_mx Some BG) Bp; FRZL FR1; data_at Tsh (tarray tdouble MAXW) (map fst θw' ++ Zrepeat Vundef (MAXW - Zlength wx)) v_theta;
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
   SEP (densematn sh (map_mx Some BG) Bp; FRZL FR1;
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
   SEP (densematn sh (map_mx Some BG) Bp; FRZL FR1;
            data_at Tsh (tarray tdouble MAXW)
                (map fst (sublist 0 w (θw'' i) ++ sublist w (Zlength θw') θw')
                ++ Zrepeat Vundef (MAXW - Zlength wx)) v_theta;
            densematn sh (map_mx Some X) Xp;
            fold_right sepcon emp (map (wx_to_wavedata sh) wx))).
+ autorewrite with sublist. entailer!!.
+
rename i0 into w.
subst POSTCONDITION. unfold abbreviate.
thaw FR1.
abbreviate_semax.
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
pose (Y := existT _ N A  :   {Nt: nat &  'rV[ftype Tdouble]_(S Nt)}).
pose (K := existT _ Nfr (Ordinal Hk) :  {Nfr & 'I_(S Nfr)}).
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
pose (Y := existT _ N σ  :   {Nt: nat &  'rV[ftype Tdouble]_(S Nt)}).
forward_call (sh,Y, σp, K).
simpl firstn.
rewrite Float_of_int_e.  replace (Z.of_nat (Ordinal Hk)) with k by (simpl; lia).
entailer!!.
rep_lia.
clear Y K.
forward.
assert (forall j, map snd (fst (iteri_upto j)) = map fst wx). {
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
   LOCAL (temp _sigma (Vfloat (interpolate σ (Ordinal Hk)));
    temp _A (Vfloat (interpolate A (Ordinal Hk)));
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
rewrite upd_Znth_app1 by list_solve.
rewrite !map_app.
rewrite upd_Znth_app2 by list_solve.
rewrite !Zlength_map.
rewrite Zlength_sublist by list_solve.
autorewrite with sublist.
rewrite (sublist_split w (w+1) (Zlength θw') θw') by list_solve.
rewrite !map_sublist.
rewrite !map_app.
rewrite upd_Znth_app1 by list_solve.
rewrite !map_sublist.
rewrite (sublist_one w (w+1)) by list_solve.
rewrite upd_Znth0.
rewrite (sublist_split 0 w (w+1)) by list_solve.
rewrite (sublist_one w (w+1)) by list_solve.
rewrite !app_assoc.
f_equal. f_equal. f_equal.
rewrite Znth_map by list_solve.
unfold iteri_upto.
pose proof (Zlength_ord_enum (S Nb)).
rewrite sublist_one by list_solve.
simpl.
replace (eqtype.eq_op _ _) with true.
change @seq.map with map.
rewrite Znth_map by list_solve.
simpl.
f_equal.
f_equal.
assert (Wave.θ0 (fst (Znth w wx)) = θ0). rewrite H3; auto.
subst θ0. clear H3. 
replace (fst (Znth w wx)) with (snd (Znth w θw)); auto.
transitivity (Znth w (map snd θw)). rewrite Hθ. list_solve. list_solve.
symmetry.
unfold eqtype.eq_op. simpl.
rewrite <- nth_Znth.
rewrite nth_seq_nth.
change (Z.to_nat 0) with (nat_of_ord (@ord0 Nb)).
rewrite mv_mathcomp.nth_ord_enum'.
simpl. lia. 
lia.
* (* i=0, k != 0 case *)
forward; try (rewrite Znth_map by list_solve; rewrite H3). 
  entailer!!. simpl local. entailer!. destruct H25; auto.
simpl.
pose (Y := existT _ N v  :   {Nt: nat &  'rV[ftype Tdouble]_(S Nt)}).
pose (K := existT _ Nfr (inord (Z.to_nat (k-1))) :  {Nfr & 'I_(S Nfr)}).
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
set (vt := interpolate v _).
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
replace (interpolate _ _) with vt. auto.
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
replace θw' with (fst (iteri_upto i)) by (rewrite H1; auto).
clear - H5 H0.
subst iteri_upto.
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
admit.
admit.
+
assert (Zlength (θw'' i) = Zlength wx) by admit. (* already proved elsewhere *)
assert (Zlength θw' = Zlength wx) by admit. (* already proved elsewhere *)
entailer!!.
f_equal. f_equal. subst ew.
rewrite map_map, sublist_map.
f_equal.
list_solve.
apply derives_refl'; f_equal.
list_solve.
Admitted.

Lemma semax_synthesize_i_loop:
 forall {Espec: OracleKind}  Nfr Nb Nbg dt (BG :  'M[ftype Tdouble]_(S Nb,S Nbg)) 
          (X:  'M[ftype Tdouble]_(S Nb, S Nfr)) 
         (Xp Bp  p v_theta: val) sh (k: Z) (wx : list (Wave.t * (val * val * val)))
 (SH : readable_share sh)
 (Hfr : Z.of_nat (S Nb * S Nfr) <= Int.max_signed)
 (Hbg : Z.of_nat (S Nb * S Nbg) <= Int.max_signed)
 (Hwx : Zlength wx <= MAXW)
 (H : 0 <= k < Z.of_nat (S Nfr))
 (Hk : Datatypes.is_true (ssrnat.leq (S (Z.to_nat k)) (S Nfr))),
let FR1 := @abbreviate _ 
  (map
    (fun i : nat =>
     freezer.my_nth i
       [data_at_ Tsh (tarray tdouble MAXW) v_theta;
        data_at sh tdata
          (Xp,
           (Bp,
            (Vint (Int.repr (Z.of_nat (S Nb))),
             (Vint (Int.repr (Z.of_nat (S Nfr))),
              (Vint (Int.repr (Z.of_nat (S Nbg))),
               (Vfloat dt, (map wx_to_waverep wx, Vint (Int.repr (Zlength (map fst wx))))))))))
          p;
        densematn sh (map_mx Some X) Xp;
        densematn sh (map_mx Some BG) Bp;
        fold_right sepcon emp (map (wx_to_wavedata sh) wx)]
       emp)
    (map Z.to_nat [1])) in 
semax (func_tycontext f_synthesize Vprog Gprog nil)
  (PROP ( )
   LOCAL (
    temp _bg_col (Vint (Int.repr (Z.of_nat (nat_of_ord (Ordinal (getBG_col Nfr Nbg (Ordinal Hk)))))));
   temp _k (Vint (Int.repr k));
   temp _energy (Vfloat (fst (snd (iterk dt BG X (map fst wx) (Z.to_nat k)))));
   temp _diff_sum (Vfloat (snd (snd (iterk dt BG X (map fst wx) (Z.to_nat k))))); 
   temp _X Xp; temp _BG Bp; temp _waves (field_address tdata (DOT _waves) p); temp _dt (Vfloat dt);
   temp _Nbg (Vint (Int.repr (S Nbg))); temp _Nfr (Vint (Int.repr (S Nfr)));
   temp _Nb (Vint (Int.repr (S Nb))); temp _Nw (Vint (Int.repr (Zlength (map fst wx))));
   lvar _theta (tarray tdouble  MAXW) v_theta; temp _data p)
   SEP (FRZL FR1;
   data_at Tsh (tarray tdouble MAXW)
       (map fst (fst (iterk dt BG X (map fst wx) (Z.to_nat k))) ++
      Zrepeat Vundef (MAXW - Zlength wx))
     v_theta;
   densematn sh (map_mx Some X) Xp; densematn sh (map_mx Some BG) Bp;
   fold_right sepcon emp (map (wx_to_wavedata sh) wx)))
  synthesize_i_loop
  (normal_ret_assert
     (PROP ( )
      LOCAL (
       temp _k (Vint (Int.repr k));
       temp _energy (Vfloat (fst (snd (iterk dt BG X (map fst wx) (Z.to_nat (k + 1))))));
       temp _diff_sum (Vfloat (snd (snd (iterk dt BG X (map fst wx) (Z.to_nat (k + 1)))))); 
       temp _X Xp; temp _BG Bp; temp _waves (field_address tdata (DOT _waves) p); temp _dt (Vfloat dt);
       temp _Nbg (Vint (Int.repr (S Nbg))); temp _Nfr (Vint (Int.repr (S Nfr)));
       temp _Nb (Vint (Int.repr (S Nb))); temp _Nw (Vint (Int.repr (Zlength (map fst wx))));
       lvar _theta (tarray tdouble MAXW) v_theta; temp _data p)
      SEP (FRZL FR1;
      data_at Tsh (tarray tdouble MAXW)
        (map fst (fst (iterk dt BG X (map fst wx) (Z.to_nat (k + 1)))) ++
         Zrepeat Vundef (MAXW - Zlength wx))
        v_theta;
      densematn sh (map_mx Some X) Xp; densematn sh (map_mx Some BG) Bp;
      fold_right sepcon emp (map (wx_to_wavedata sh) wx)))).
Proof.
intros.
rewrite Zlength_map.
assert (Hbgcol :=bg_col_range Nfr Nbg (Ordinal Hk)).
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
 extensionality x. destruct x; simpl; auto.
}
destruct u as [θw [energy diff_sum]] eqn:?H.
assert (Hk0: k <> 0 -> Forall (is_float oo fst) θw). {
 intro; subst u.
 destruct (Z.to_nat k) eqn:?H; [ lia | ].
 clear - H0. simpl in H0.
 destruct (ord_enum (S (Nfr))) eqn:?H.
 pose proof (mv_mathcomp.size_ord_enum (S Nfr)).  rewrite H in H1; inv H1. 
 admit. (* looks fine *)
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
set (iteri_upto i := seq.foldl (one_iteri dt BG X (Ordinal Hk)) (θw, (energy, diff_sum)) (sublist 0 i (ord_enum (S Nb)))).
set (θw'' i := fst (iteri_upto (i+1))).
forward_for_simple_bound (Z.of_nat (S Nb)) (EX i:Z,
     (PROP ( )
      LOCAL (
       temp _bg_col (Vint (Int.repr (Z.of_nat (nat_of_ord (Ordinal (getBG_col Nfr Nbg (Ordinal Hk)))))));
      temp _k (Vint (Int.repr k));
      temp _energy
        (Vfloat (fst (snd (iteri_upto i))));
      temp _diff_sum (Vfloat (snd (snd (iteri_upto i))));
      temp _X Xp; temp _BG Bp; temp _waves (field_address tdata (DOT _waves) p); temp _dt (Vfloat dt);
      temp _Nbg (Vint (Int.repr (Z.of_nat (S Nbg)))); temp _Nfr (Vint (Int.repr (Z.of_nat (S Nfr))));
      temp _Nb (Vint (Int.repr (Z.of_nat (S Nb)))); temp _Nw (Vint (Int.repr (Zlength wx)));
      lvar _theta (tarray tdouble MAXW) v_theta; temp _data p)
      SEP (FRZL FR1;
      data_at Tsh (tarray tdouble MAXW)
        (map fst (fst (iteri_upto i)) ++ Zrepeat Vundef (MAXW - Zlength wx))
        v_theta;
      densematn sh (map_mx Some X) Xp; densematn sh (map_mx Some BG) Bp;
      fold_right sepcon emp (map (wx_to_wavedata sh) wx)))).
- autorewrite with sublist. simpl seq.foldl. entailer!!.
-
set (j' := Ordinal  (getBG_col Nfr Nbg (Ordinal Hk))) in *.
assert (Hi: Datatypes.is_true (ssrnat.leq (S (Z.to_nat i)) (S (Nb)))) by admit.
set (i' := Ordinal Hi).
forward_densematn_get (map_mx Some BG) i' j' Bp sh (BG i' j').
 entailer!!. simpl. rewrite (Z2Nat.id i) by lia. rewrite (Z2Nat.id k) by lia. rewrite Z2Nat.id; auto.
pose proof (bg_col_is Nbg H Hk). fold j' in H1.
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
set (ew := map (fun f: matrix (ftype Tdouble) (S Nb) 1%nat => fun_of_matrix f i' ord0) (map (waveform dt (Ordinal Hk)) (θw'' i))).
eapply semax_seq.
+
apply semax_synthesize_w_loop; auto.
assumption.
rewrite <- H1; reflexivity.
+
admit.
-
unfold iteri_upto.
pose proof (Zlength_ord_enum (S Nb)).
rewrite (sublist_same 0 (Z.of_nat (S Nb))) by list_solve.
entailer!!.
all: fail.
Admitted.

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
assert_PROP (Z.of_nat (S Nb * S Nfr)  <= Int.max_signed /\ Z.of_nat (S Nb * S Nbg) <= Int.max_signed
                          /\ Zlength wx <= MAXW). {
  entailer!. split. lia.
 simplify_value_fits in H2.
 decompose [and] H2; clear H2. simplify_value_fits in H16.
 rewrite <- MAXW_eq in H16.
 destruct H16. clear - H2. list_solve.
}
destruct H as [Hfr [Hbg Hwx]].
freeze FR1 := (data_at _ tdata _ p).
replace (Float.of_bits (Int64.repr 0)) with (Zconst Tdouble 0) by prove_float_exprs_equal.
forward_for_simple_bound (Z.of_nat (S Nfr)) 
  (EX k:Z, 
   PROP()
   LOCAL (temp _energy (Vfloat (fst (snd (iterk dt BG X (map fst wx) (Z.to_nat k)))));
   temp _diff_sum (Vfloat (snd (snd (iterk dt BG X (map fst wx) (Z.to_nat k)))));
   temp _X Xp; temp _BG Bp; temp _waves (field_address tdata (DOT _waves) p); temp _dt (Vfloat dt);
   temp _Nbg (Vint (Int.repr (S Nbg))); temp _Nfr (Vint (Int.repr (S Nfr)));
   temp _Nb (Vint (Int.repr (S Nb))); temp _Nw (Vint (Int.repr (Zlength (map fst wx))));
   lvar _theta (tarray tdouble MAXW) v_theta; temp _data p)
   SEP (FRZL FR1; 
   data_at Tsh (tarray tdouble MAXW) 
       (map fst (fst (iterk dt BG X (map fst wx) (Z.to_nat k))) ++ Zrepeat Vundef (MAXW-Zlength wx)) v_theta; 
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
pose proof (bg_col_is Nbg H Hk).
forward.
entailer!!.
repeat change (Z.pos (PosDef.Pos.of_succ_nat ?A)) with (Z.of_nat (S A)).
rewrite !inj_S. unfold Z.succ. rewrite !Z.add_simpl_r.
rewrite (Float_to_int_e _ _ H0).
entailer!!.
replace (force_val _) with (Vint (Int.repr (Z.of_nat (Ordinal (getBG_col Nfr Nbg (Ordinal Hk)))))).
2:{
simpl force_val.
rewrite !sub_repr.
unfold sem_cast, classify_cast, tint, tdouble, sem_cast_f2i, cast_float_int, cast_int_int.
repeat change (Z.pos (PosDef.Pos.of_succ_nat ?A)) with (Z.of_nat (S A)).
rewrite !inj_S. unfold Z.succ. rewrite !Z.add_simpl_r.
rewrite H0. reflexivity.
}
clear H0.
unfold abbreviate in FR1.

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

