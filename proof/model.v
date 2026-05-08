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

From mathcomp Require Import Rstruct.

Require LAProof.accuracy_proofs.export.
Module F := LAProof.accuracy_proofs.mv_mathcomp.F.

Require Import CWA.float_lemmas.

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
  Hfr: 1 < Z.of_nat Nfr.+1 /\ Z.of_nat (Nb.+1 * Nfr.+1) <= Int.max_signed;
  Hbg: Z.of_nat (Nb.+1 * Nbg.+1) <= Int.max_signed
}.
End Data.

Definition Fsum {NAN: FPCore.Nans} {t: type} (base: ftype t) [n: nat] (f: 'I_n -> ftype t) : ftype t :=
  foldl BPLUS base (map f (ord_enum n)).

Definition M_PI : ftype Tdouble := 3.141592653589793%F64.

Definition L := BMULT (Zconst Tdouble 2) M_PI.

Definition range2pi (x: ftype Tdouble) : ftype Tdouble :=
    BMINUS x (BMULT L (BFLOOR (BDIV x L))).

Definition wrap (x: ftype Tdouble) : ftype Tdouble :=
   BMINUS (range2pi (BPLUS x M_PI)) M_PI.

Definition interp_aux (n Nfr: nat) (k: nat) : nat :=
  Z.to_nat (Binary.Btrunc _ _ (BFLOOR (BMULT (BDIV (Zconst _ (Z.of_nat k)) (Zconst _ (Z.of_nat Nfr))) 
                                                               (Zconst Tdouble (Z.of_nat n))))).

Lemma interp_aux1: forall [Nfr n]  (Hfr: 1 < Z.of_nat (Nfr.+1)<=Int.max_signed) (Hn: Z.of_nat (n.+1) <= Int.max_signed) (k: 'I_Nfr.+1) ,
    is_true (leq (S (interp_aux n Nfr k)) (n.+1)).
Proof.
intros.
unfold interp_aux.
set (x := BMULT _ _).
destruct (interpolate_range Hfr Hn k).
fold x in H,H0. destruct H0. clearbody x.
pose proof Btrunc_range_pos (Z.of_nat n) (BFLOOR x) ltac:(rep_lia).
spec H2; [ clear H2; split | ].
-
clear - H H0.
apply BFLOOR_le'; auto.
compute; split; congruence.
-
apply Fle_trans with x; auto.
apply BFLOOR_le; auto.
-
spec H2. apply BFLOOR_finite; auto.
lia.
Qed.

Definition interpolate [n Nfr: nat] (Hfr: 1 < Z.of_nat (Nfr.+1)<=Int.max_signed) (Hn: Z.of_nat (n.+1) <= Int.max_signed)  (y: 'rV[ftype Tdouble]_n.+1) (k: 'I_Nfr.+1) : ftype Tdouble :=
  let a := BMULT (BDIV (Zconst _ (Z.of_nat k)) (Zconst _ (Z.of_nat Nfr))) (Zconst Tdouble (Z.of_nat n)) in
  let j := Binary.Btrunc _ _ (BFLOOR a) in
  let j' := @Ordinal n.+1 (Z.to_nat j) (interp_aux1 Hfr Hn k) in
  (if  (Z.to_nat (j + 1) < n.+1)%N as b return (leq (S (Z.to_nat (j + 1))) n.+1 = b -> ftype Tdouble)
   then fun H0 :  (Z.to_nat (j + 1) < n.+1)%N = true => ((Zconst _ (j+1) - a) * y ord0 j' + (a-Zconst _ j) * y ord0 (Ordinal H0))%F64
   else fun=> y ord0 j') erefl.

Lemma getBG_col: forall [Nfr Nbg: nat]
    (H0: 1 < Z.of_nat (S Nfr) <= Int.max_signed)
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
pose proof (Btrunc_range_pos (Z.of_nat Nbg) j ltac:(rep_lia) H Hj).
subst c.
set (i := Binary.Btrunc _ _ j) in H,H2|-*. clearbody i.
lia.
Qed.

Lemma N_range: forall [Nb N] (H: 1 < Z.of_nat N.+1 /\  Z.of_nat (S Nb * S N) <= Int.max_signed),
        1 < Z.of_nat N.+1 /\  Z.of_nat (S N) <= Int.max_signed.
Proof. rep_lia. Qed.

Lemma N_range1: forall [Nb N] (H: 1 < Z.of_nat N.+1 /\  Z.of_nat (S Nb * S N) <= Int.max_signed),
        Z.of_nat (S Nb) <= Int.max_signed.
Proof. rep_lia. Qed.

Lemma N_range2: forall [Nb N] (H: Z.of_nat (S Nb * S N) <= Int.max_signed),
        Z.of_nat (S N) <= Int.max_signed.
Proof. rep_lia. Qed.

Definition a_wave : Wave.t.
Proof. apply (Wave.Build_t O (const_mx 0%F64) (const_mx 0%F64)  (const_mx 0%F64)  0%F64 ltac:(rep_lia)).
Qed.

Lemma col_maj_aux m n : (\sum_(i<n) m = (m * n)%N) * (1 = 1)%N.
Proof.
intros.
split; auto.
clear.
rewrite (unlock bigop_unlock)
          /reducebig.
rewrite  /comp /applybig /= mv_mathcomp.index_ord_enum.
transitivity (foldr (fun=>[eta addn m]) 0%N (map (fun=> tt) (ord_enum n))).
symmetry; apply foldr_map.
assert (size [seq tt | _ <- ord_enum n] = n).
rewrite size_map mv_mathcomp.size_ord_enum //.
set (al := [seq tt | _ <- ord_enum n]) in H|-*. clearbody al.
subst n.
induction al; simpl. lia.
rewrite IHal.
lia.
Qed.

Definition col_maj [m n T] (A: 'M[T]_(m,n)) : 'cV[T]_(m*n) :=
  castmx (col_maj_aux _ _) (\mxcol_(j<n) col j A).

Lemma col_majE: forall {t} [m n] (X: 'M[t]_(m,n)) (i: 'I_m) (j: 'I_n) (ij: 'I_(m*n)),
     (nat_of_ord ij = nat_of_ord i + nat_of_ord j * m)%N ->
  fun_of_matrix (col_maj X) ij ord0 = fun_of_matrix X i j.
Admitted.

Lemma col_majE': forall {t} [m n] (X: 'M[t]_(m,n)) (i: 'I_m) (j: 'I_n)
    (H : (i + j * m < m * n)%N),
  fun_of_matrix (col_maj X) (Ordinal H) ord0 = fun_of_matrix X i j.
Proof.
intros.
apply col_majE. simpl. lia.
Qed.

Module Fmodel.

Section DATA.
Variable D: Data.t.
Let Nb := Data.Nb D.
Let Nfr := Data.Nfr D.
Let Nbg := Data.Nbg D.
Let BG := Data.BG D.
Let waves := Data.waves D.
Let Hfr: 1 < Z.of_nat (Data.Nfr D).+1 /\ Z.of_nat ((Data.Nb D).+1 * (Data.Nfr D).+1) <= Int.max_signed := Data.Hfr D.
Let Hbg : Z.of_nat (Nb.+1 * Nbg.+1) <= Int.max_signed := Data.Hbg D.
Let Nw : nat := seq.size waves.
Let dt := Data.dt D.

Definition W : 'cV[Wave.t]_Nw := \col_w seq.nth a_wave waves w.

Definition v (w: 'I_Nw) (k: 'I_Nfr.+1) : ftype Tdouble :=
   interpolate  (N_range Hfr) (Wave.Hn (W w ord0)) (Wave.v (W w ord0)) k.

Definition A (w: 'I_Nw) (k: 'I_Nfr.+1) : ftype Tdouble :=
   interpolate  (N_range Hfr) (Wave.Hn (W w ord0)) (Wave.A (W w ord0)) (inord k).

Definition σ  (w: 'I_Nw) (k: 'I_Nfr.+1) : ftype Tdouble :=
   interpolate  (N_range Hfr) (Wave.Hn (W w ord0)) (Wave.σ (W w ord0)) (inord k).

Definition θw  (w: 'I_Nw) (k: 'I_Nfr.+1) : ftype Tdouble :=
  foldl (fun (x: ftype Tdouble) (j: 'I_Nfr.+1) => range2pi (x + v w j * dt)%F64) (Wave.θ0 (W w ord0)) (take k (ord_enum Nfr.+1)).

Definition dx (w: 'I_Nw) (i: 'I_Nb.+1) (k: 'I_Nfr.+1) : ftype Tdouble :=
    wrap (Zconst Tdouble (Z.of_nat i) * (L / Zconst Tdouble (Z.of_nat Nb.+1)) - θw w k)%F64.

Definition waveform (w: 'I_Nw)  (i: 'I_Nb.+1) (k: 'I_Nfr.+1) : ftype Tdouble :=
    (A w k * Bexp (- ((dx w i k * dx w i k) / (Zconst Tdouble 2 * (σ w k * σ w k)))))%F64.

Definition BGval (i: 'I_Nb.+1) (k: 'I_Nfr.+1) : ftype Tdouble :=
      BG i (Ordinal  (getBG_col (N_range Hfr)  (N_range2 Hbg) k)).

Definition signal (i: 'I_Nb.+1) (k: 'I_Nfr.+1) : ftype Tdouble :=
      Fsum (BGval i k) (fun w: 'I_(Nw) => waveform w i k).

Definition energy_sum := 
    Fsum common.pos_zero (fun k => BABS (col_maj (Data.X D) k ord0)).

Definition diff_sum := 
   Fsum common.pos_zero (fun k => BABS (col_maj (\matrix_(i,k) (Data.X D i k - signal i k)%F64) k ord0)).

Definition result := (diff_sum / energy_sum)%F64.

End DATA.
End Fmodel.

Module Rmodel.
Section DATA.
Variable D: Data.t.
Let Nb := Data.Nb D.
Let Nfr := Data.Nfr D.
Let Nbg := Data.Nbg D.
Let BG := Data.BG D.
Let waves := Data.waves D.
Let Hfr: 1 < Z.of_nat (Data.Nfr D).+1 /\ Z.of_nat ((Data.Nb D).+1 * (Data.Nfr D).+1) <= Int.max_signed := Data.Hfr D.
Let Hfr':  1 < Z.of_nat Nfr.+1 /\  Z.of_nat (S Nfr) <= Int.max_signed := N_range Hfr.
Let Hbg : Z.of_nat (Nb.+1 * Nbg.+1) <= Int.max_signed := Data.Hbg D.
Let Nw : nat := seq.size waves.
Let dt := Data.dt D.
Import Rdefinitions Rcomplements.
Import Fmodel.

Coercion Z.of_nat : nat >-> Z.
Coercion IZR: Z >-> R.
Coercion FT2R: ftype >-> R.

Definition interpolate [n Nfr: nat] (Hfr: (1 < Z.of_nat (Nfr.+1)<=Int.max_signed)%Z) (Hn: (Z.of_nat (n.+1) <= Int.max_signed)%Z)
         (y: 'rV[ftype Tdouble]_n.+1) (k: 'I_Nfr.+1) : R :=
  let a := (k / IZR Nfr)*n in let j := floor a
    in  if (j <? n)%Z 
         then ((j+1)-a) * y ord0 (inord (Z.to_nat j)) + (a-j)*(y ord0 (inord (Z.to_nat j+1)))
         else  y ord0 (inord (Z.to_nat j)).

Definition v (w: 'I_Nw) (k: 'I_Nfr.+1) : R :=
   interpolate  Hfr' (Wave.Hn (W D w ord0)) (Wave.v (W D w ord0)) k.

Definition A (w: 'I_Nw) (k: 'I_Nfr.+1) : R :=
   interpolate Hfr' (Wave.Hn (W D w ord0)) (Wave.A (W D w ord0)) (inord k).

Definition σ (w: 'I_Nw) (k: 'I_Nfr.+1) : R :=
   interpolate  Hfr' (Wave.Hn (W D w ord0)) (Wave.σ (W D w ord0)) (inord k).

Definition range2pi (x: R) : R :=
            x-L*floor(x/L).

Definition wrap (x: R) : R :=
     range2pi (x+Rtrigo1.PI) - Rtrigo1.PI .

Definition θw (w: 'I_Nw) (k: 'I_Nfr.+1) : R :=
  foldl (fun (x: R) (j: 'I_Nfr.+1) => range2pi (x + v w j * FT2R dt)) (FT2R (Wave.θ0 (W D w ord0))) (take k (ord_enum Nfr.+1)).

Definition dx (w: 'I_Nw) (i: 'I_Nb.+1) (k: 'I_Nfr.+1) : R :=
     wrap ( i * (L / IZR Nb.+1) - θw w k).

Definition waveform (w: 'I_Nw) (i: 'I_Nb.+1) (k: 'I_Nfr.+1) : R :=
  (A w k * Rtrigo_def.exp (- ((dx w i k * dx w i k) / (2 * (σ w k * σ w k))))).

Definition signal  (i: 'I_Nb.+1) (k: 'I_Nfr.+1) : R :=
  \big[Rplus/0]_(w' < 1+Nw) 
          match split w' with
           | inl _ => FT2R (BGval D i k)
           | inr w => waveform w i k
           end.

Definition energy_sum := \big[Rplus/0]_k  Rbasic_fun.Rabs(col_maj (Data.X D) k ord0).

Definition diff_sum := 
   \big[Rplus/0]_k Rbasic_fun.Rabs (col_maj  (\matrix_(i,k) (Data.X D i k - signal i k)%R) k ord0).

Definition result_real := diff_sum / energy_sum.

End DATA.
End Rmodel.

Module Pmodel.

Section DATA.
Variable D: Data.t.
Let Nb := Data.Nb D.
Let Nfr := Data.Nfr D.
Let Nbg := Data.Nbg D.
Let dt := Data.dt D.
Let BG := Data.BG D.
Let waves := Data.waves D.
Let Hfr: 1 < Z.of_nat (Data.Nfr D).+1 /\ Z.of_nat ((Data.Nb D).+1 * (Data.Nfr D).+1) <= Int.max_signed := Data.Hfr D.
Let Hfr':  1 < Z.of_nat Nfr.+1 /\  Z.of_nat (S Nfr) <= Int.max_signed := N_range Hfr.
Let Hbg : Z.of_nat (Nb.+1 * Nbg.+1) <= Int.max_signed := Data.Hbg D.
Let Hbg' : Z.of_nat Nbg.+1 <= Int.max_signed := N_range2 Hbg.
Let Nw : nat := seq.size waves.

Definition waveform (k: 'I_Nfr.+1)  (θw: Values.val * Wave.t) : 'cV[ftype Tdouble]_Nb.+1 :=
 match θw with
 | (Vfloat θ, w) => 
  let A := interpolate Hfr' (Wave.Hn w) (Wave.A w) k in
  let σ := interpolate Hfr' (Wave.Hn w) (Wave.σ w) k in
  \col_i 
   let dx := wrap (BMINUS (BMULT (Zconst Tdouble (Z.of_nat i)) (BDIV L (Zconst _ (Z.of_nat Nb.+1)))) θ) in
     BMULT A (Bexp (BOPP (BDIV (BMULT dx dx) (BMULT (Zconst _ 2) (BMULT σ σ)))))
 | _ => const_mx (Zconst _ 0)
 end.
 
Definition updateθ  (k: 'I_Nfr.+1) (θw: Values.val * Wave.t) : Values.val * Wave.t :=
 match θw with
 | (Vfloat θ, w) =>
  let v := interpolate Hfr' (Wave.Hn w) (Wave.v w) (@inord Nfr (k-1)%N) in
   (Vfloat (range2pi (@BPLUS _ Tdouble θ (BMULT v dt))), w)
 | (_, w) => (Vundef, w)
 end.

Definition one_iterk:
     (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) ->
      ('I_Nfr.+1) ->
     (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) :=
fun '(θw, (energy, diff_sum)) k =>
  let e_bg := col (Ordinal  (getBG_col Hfr' Hbg' k)) BG
  in let θw' := if k==ord0 
                 then map (fun w => (Vfloat (Wave.θ0 (snd w)), snd w)) θw
                 else map (updateθ k) θw
  in let ew := map (waveform k) θw'
  in let e := foldl (F.addmx (n:=1)) e_bg ew
  in let energy' := foldl BPLUS energy (map (fun j => BABS (Data.X D j k)) (ord_enum Nb.+1))
  in let d' := foldl BPLUS diff_sum (map (fun j => BABS (BMINUS (Data.X D j k) (e j ord0))) (ord_enum Nb.+1))
  in (θw', (energy', d')).

Definition initial_values (waves: list Wave.t) :  (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) :=
 (map (fun w => (Vundef, w)) waves, (Zconst _ 0, Zconst _ 0)).

Definition iterk (waves: list Wave.t) (k: nat) : 
     (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) :=
 foldl one_iterk (initial_values waves) (take k (ord_enum Nfr.+1)).

Definition one_iteri
      (k: 'I_Nfr.+1) :
     (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) -> 'I_Nb.+1 ->
     (list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)) :=
 fun '(θw, (energy, diff_sum)) (i: 'I_Nb.+1) =>
   let θw' := if i==ord0
                   then if k==ord0 
                         then map (fun w => (Vfloat (Wave.θ0 (snd w)), snd w)) θw
                         else map (updateθ k) θw
                   else θw
    in let ew : seq (ftype Tdouble) := map (fun f: 'cV_Nb.+1 => f i ord0) (map (waveform k) θw') 
    in let e_bg := BG i (Ordinal (getBG_col Hfr' Hbg' k))
    in let e : ftype Tdouble:= foldl BPLUS e_bg ew
    in let Xik := Data.X D i k
    in let energy' := BPLUS energy (BABS Xik)
    in let d' := BPLUS diff_sum (BABS (BMINUS Xik e))
    in (θw', (energy', d')).

Definition all_iteri: forall  (k: 'I_Nfr.+1) (state: list (Values.val * Wave.t) * (ftype Tdouble * ftype Tdouble)),
   foldl (one_iteri k) state (ord_enum Nb.+1) = one_iterk state k.
Proof.
intros.
unfold one_iterk.
destruct state as [θw [energy diff_sum]].
set u := if _ then _ else _.
rewrite -(cat_take_drop 1 (ord_enum (S Nb))).
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
set f := map (waveform _) _.
replace (fun_of_matrix (foldl _ (col _ _) _) _ _)
 with (foldl BPLUS (fun_of_matrix BG ord0 (Ordinal (getBG_col Hfr' Hbg' k)))
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
simpl.
rewrite mxE //.
rewrite /= IHl !mxE //.
}
set d1 := BPLUS diff_sum _.
clearbody d1.
revert H0.
rewrite -(revK l).
set (r := rev l).

clearbody r. clear l.
rewrite take0. simpl cat. rewrite drop0.
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

Definition synth_err: ftype Tdouble :=
  let '(_, (energy, diff_sum)) := iterk waves Nfr.+1
   in  (diff_sum / energy)%F64.

End DATA.
End Pmodel.

Module Pmodel_Fmodel.
Section DATA.
Variable D: Data.t.
Let Nb := Data.Nb D.
Let Nfr := Data.Nfr D.
Let Nbg := Data.Nbg D.
Let dt := Data.dt D.
Let BG := Data.BG D.
Let waves := Data.waves D.
Let Hfr: 1 < Z.of_nat (Data.Nfr D).+1 /\ Z.of_nat ((Data.Nb D).+1 * (Data.Nfr D).+1) <= Int.max_signed := Data.Hfr D.
Let Hfr':  1 < Z.of_nat Nfr.+1 /\  Z.of_nat (S Nfr) <= Int.max_signed := N_range Hfr.
Let Hbg : Z.of_nat (Nb.+1 * Nbg.+1) <= Int.max_signed := Data.Hbg D.
Let Hbg' : Z.of_nat Nbg.+1 <= Int.max_signed := N_range2 Hbg.
Let Nw : nat := seq.size waves.
Let X := Data.X D.

Definition θw_prev (w: 'I_Nw) (k:  nat) : Values.val :=
    if (k==O) then Vundef else Vfloat (Fmodel.θw D w (inord (k-1))).

Lemma map_ord_enum_inord:
  forall {T} (f: nat -> T) (n: nat), map (comp f (@nat_of_ord n)) (ord_enum n) = map f (iota 0 n).
Proof.
clear.
intros.
rewrite map_comp.
f_equal.
rewrite <- val_ord_enum.
simpl.
auto.
Qed.
Definition diff : 'M_(Nb.+1,Nfr.+1) := \matrix_(i,k) (BMINUS (X i k) (Fmodel.signal D i k)).

Lemma Fmodel_signal_eq:
 forall (k: 'I_Nfr.+1) (i: 'I_Nb.+1),
  Fmodel.signal D i k =
fun_of_matrix
  (foldl (float_lemmas.F.addmx (n:=1)) (col (Ordinal (getBG_col (N_range Hfr) (N_range2 Hbg) k)) BG)
     [seq Pmodel.waveform D k i
        | i <- if k == ord0
               then
                [seq (Vfloat (Wave.θ0 w.2), w.2)
                   | w <- [seq (θw_prev w k, nth a_wave waves (nat_of_ord w)) | w <- ord_enum Nw]]
               else
                [seq Pmodel.updateθ D k i
                   | i <- [seq (θw_prev w k, nth a_wave waves (nat_of_ord w)) | w <- ord_enum Nw]]])
  i ord0.
Proof.
intros.
unfold Fmodel.signal.
unfold Fmodel.BGval, Fmodel.waveform. fold waves. fold BG. fold Hfr. fold Hbg.
set c := Ordinal _. clearbody c.
unfold Fsum.
fold Nw.
replace (fun_of_matrix BG i c) with (col c BG i ord0) by apply mxE.
set BGc := col c BG.
set BGci := BGc i ord0.
assert (BGci = BGc i ord0) by reflexivity.
clearbody BGc. clearbody BGci. clear c BG.
replace         (if eq_op k ord0
            then
             map (fun w : prod Values.val Wave.t => pair (Vfloat (Wave.θ0 (snd w))) (snd w))
               (map (fun w : ordinal Nw => pair (θw_prev w (nat_of_ord k)) (nth a_wave waves (nat_of_ord w))) (ord_enum Nw))
            else
             map (fun i0 : prod Values.val Wave.t => Pmodel.updateθ D k i0)
               (map (fun w : ordinal Nw => pair (θw_prev w (nat_of_ord k)) (nth a_wave waves (nat_of_ord w))) (ord_enum Nw)))
 with (map (if eq_op k ord0 then (fun w =>  pair (Vfloat (Wave.θ0 (snd w))) (snd w))
              else Pmodel.updateθ D k)
           (map (fun w : ordinal Nw => pair (θw_prev w (nat_of_ord k)) (nth a_wave waves (nat_of_ord w)))
              (ord_enum Nw)))
   by (destruct (eq_op k ord0); auto).
 rewrite -!map_comp /comp.
 revert BGc BGci H;  induction (ord_enum Nw); intros; auto.
 change (map ?F (cons a l)) with (F a :: map F l).
 repeat change (foldl ?F ?A (cons ?B ?L)) with (foldl F (F A B) L).
 apply IHl. clear IHl.
 unfold F.addmx. rewrite mxE -H.
 f_equal.
 clear BGc BGci H l.
 unfold Fmodel.A, Fmodel.dx, Fmodel.σ.
unfold Pmodel.waveform.
unfold θw_prev.
unfold Fmodel.θw.
unfold Fmodel.v.
 set (w := Fmodel.W D a ord0).
 replace (nth a_wave waves (nat_of_ord a)) with w
   by (subst w; unfold Fmodel.W; rewrite mxE; auto).
clearbody w.
simpl in w.
rewrite inord_val.
change (eq_op (nat_of_ord k) O) with (eq_op k ord0).
destruct (eq_op k ord0) eqn:?H.
-
fold (is_true (k==ord0)) in H.
rewrite boolp.eq_opE in H. subst k.
rewrite take0.
change (nat_of_ord ord0) with O.
rewrite !mxE.
f_equal.
-
unfold eq_op in H. simpl in H.
rewrite !mxE.
f_equal. f_equal.
f_equal.
f_equal.
set (u := wrap _).
set (v := wrap _).
assert (u=v); [ | congruence].
subst u v.
f_equal.
f_equal.
set (f := interpolate _ _ _).
fold dt. fold Nfr.
set (r := fun _ => _).
change (range2pi _) with (r (foldl r (Wave.θ0 w) (take (nat_of_ord (@inord Nfr (subn (nat_of_ord k) 1))) (ord_enum (S Nfr))))
  (inord (subn (nat_of_ord k) 1))).
clearbody r.
set z := Wave.θ0 w.
clearbody z.
clear - H.
pose proof (ltn_ord k).
replace (nat_of_ord (inord (subn (nat_of_ord k) 1))) with (nat_of_ord k - 1)%N; [ | rewrite inordK; lia].
replace (take (nat_of_ord k) (ord_enum (S Nfr)))
   with (take (subn (nat_of_ord k) 1) (ord_enum (S Nfr)) ++ [:: inord (k-1)]).
rewrite foldl_cat; auto.
rewrite <- (cat_take_drop (k-1) (take k (ord_enum (S Nfr)))).
f_equal.
rewrite take_takel. auto. lia.
replace (take (nat_of_ord k) (ord_enum (S Nfr))) with (take (addn 1 (subn k 1)) (ord_enum (S Nfr)))
  by (f_equal; lia).
rewrite -take_drop.
transitivity  [:: nth ord0 (ord_enum (S Nfr)) (nat_of_ord (@inord Nfr (k-1)))].
f_equal. rewrite mv_mathcomp.nth_ord_enum'. auto.
rewrite -(map_nth_iota ord0).
2: rewrite mv_mathcomp.size_ord_enum; lia.
simpl.
f_equal.
f_equal.
rewrite inordK; lia.
Qed.

Lemma OK_iterk_partial: forall k: nat, 
   (k <= Nfr.+1)%N ->
  foldl (Pmodel.one_iterk D) (Pmodel.initial_values waves) (take k (ord_enum Nfr.+1)) = 
    (map (fun w => (θw_prev w k, nth a_wave waves w)) (ord_enum Nw), 
      (Fsum common.pos_zero (fun j : 'I_(Nb.+1 * k) => BABS (fun_of_matrix (col_maj X) (inord j) ord0)),
       Fsum common.pos_zero (fun j : 'I_(Nb.+1 * k) => BABS (fun_of_matrix (col_maj diff) (inord j) ord0)))).
Proof.
unfold Pmodel.initial_values.
change (Zconst Tdouble 0) with (@common.pos_zero Tdouble).
unfold Fsum.
induction k; intros.
-
simpl.
replace (muln _ O) with O by lia.
rewrite take0 //.
unfold foldl.
f_equal.
pose proof mv_mathcomp.nth_ord_enum_lemma a_wave waves.
etransitivity.
rewrite H0; reflexivity.
unfold comp.
fold waves Nw.
unfold θw_prev.
rewrite eq_refl.
rewrite -map_comp //.
-
rewrite (@take_nth _ (@ord0 Nfr)); [  |rewrite mv_mathcomp.size_ord_enum //].
rewrite foldl_rcons.
rewrite {}IHk; [ | lia].
unfold Pmodel.one_iterk.
f_equal.
+
mv_mathcomp.ordify Nfr.+1 k.
rewrite mv_mathcomp.nth_ord_enum'.
destruct (_ == _) eqn:?H.
*
change(is_true (k == ord0)) in H0.
rewrite boolp.eq_opE in H0. subst k.
rewrite -map_comp /comp.
simpl.
f_equal.
extensionality w.
unfold θw_prev.
Import mv_mathcomp.
change (1%N==0%N) with false. simpl.
f_equal.
f_equal.
simpl.
unfold Fmodel.θw.
rewrite inordK; [ | lia].
change (subn _ _) with O.
rewrite take0.
simpl.
f_equal.
unfold Fmodel.W.
rewrite mxE.
reflexivity.
*
rewrite -map_comp /comp.
f_equal.
extensionality w.
unfold Pmodel.updateθ.
unfold θw_prev at 1.
assert (nat_of_ord k == nat_of_ord (@ord0 Nfr) = false) by (destruct (k == ord0) eqn:?H; auto).
simpl in H1. rewrite H1.
f_equal.
unfold θw_prev.
replace (_ == _) with false by (destruct ((nat_of_ord k).+1 == 0)%N eqn:?H; lia).
f_equal.
replace ((nat_of_ord k).+1-1)%N with (((nat_of_ord k)-1)+1)%N by lia.
unfold Fmodel.θw.
rewrite !inordK; try lia.
rewrite takeD.
rewrite foldl_cat.
set (u := foldl _ (Wave.θ0 _) _). clearbody u.
fold Nfr.
replace (take 1 (drop (nat_of_ord k - 1) (ord_enum Nfr.+1))) with [::nth ord0 (ord_enum Nfr.+1) (nat_of_ord k-1)].
2:{
assert (nat_of_ord k - 1 < size (ord_enum Nfr.+1))%N by (rewrite size_ord_enum; lia).
clear - H1 H2.
forget (ord_enum Nfr.+1) as al.
forget (nat_of_ord k - 1)%N as i.
clear - H1 H2.
revert i H1 H2; induction al; destruct i;  simpl; intros; auto; try lia.
rewrite take0//.
}
simpl.
f_equal.
f_equal.
unfold Fmodel.v.
f_equal. 
fold waves.
f_equal.
f_equal.
rewrite mxE.
replace (nat_of_ord k - 1)%N with (nat_of_ord (@inord Nfr (k-1))).
2: rewrite inordK; lia.
rewrite nth_ord_enum'.
rewrite inordK; try lia.
auto.
+
f_equal.
*
fold Nb. fold X.
fold Nfr in X|-*. fold Nb in X|-*.
fold addn.
change (_ Nfr (_ Nb (S Nfr))) with (addn Nfr (muln Nb (S Nfr))).
pose proof (@nth_ord_enum' (S Nfr)) (Ordinal H) ord0. simpl in H0. rewrite {}H0.
rewrite -foldl_cat.
f_equal.
clearbody X.
 clear - H. clearbody Nb. clearbody Nfr. clear - H.
set f := fun _ => _.
set g := fun _ => _.
set h := fun _ => _.
change f with (comp (fun i => BABS (col_maj X (@inord (Nfr+(Nb*Nfr.+1)) i) ord0)) (@nat_of_ord (muln (S Nb) k))). clear f.
change h with (comp (fun i => BABS (fun_of_matrix (col_maj X) (inord i) ord0)) (@nat_of_ord (muln (S Nb) (S k)))). clear h.
replace g with (comp (fun i => BABS (X (inord i) (Ordinal H))) (@nat_of_ord (S Nb))) 
  by (extensionality i; subst g; simpl; f_equal; f_equal; apply inord_val).
clear g.
rewrite !map_ord_enum_inord.
set f := fun _ => _.
replace (map _ (iota 0 (S Nb))) with (map f (iota (muln (S Nb) k) (S Nb))).
rewrite -map_cat - iotaD. f_equal. f_equal. lia. subst f.
replace (iota (muln (S Nb) k) (S Nb)) with (iota (addn (muln (S Nb) k) 0) (S Nb)) by (f_equal; lia).
rewrite iotaDl.
rewrite -map_comp.
apply eq_in_map.
intros i H0.
rewrite mem_iota in H0. simpl in H0. replace (addn 0 (S Nb)) with (S Nb) in H0 by lia.
replace (inord i) with (Ordinal H0) by (apply ord_inj; rewrite inordK; auto).
rewrite /comp.
f_equal.
apply col_majE.
simpl. etransitivity. apply inordK. nia. lia.
*
fold X.
fold Nfr in X|-*. fold Nfr in Hfr, X|-*. fold Nb in BG, Hfr,X|-*. fold Nbg in Hbg,BG|-*.
fold Hfr. fold Hbg. fold BG. clearbody BG.
fold addn.
change (_ Nfr (_ Nb (S Nfr))) with (addn Nfr (muln Nb (S Nfr))).
pose proof (@nth_ord_enum' (S Nfr)) (Ordinal H) ord0. simpl in H0. rewrite {}H0.
rewrite -foldl_cat.
f_equal.
clearbody X.
clearbody Hfr. clearbody Hbg. fold Nb.
set f := fun _ => _.
set g := fun _ => _.
set h := fun _ => _.
change f with (comp (fun i => BABS (col_maj diff (@inord (Nfr+(Nb*Nfr.+1)) i) ord0)) (@nat_of_ord (muln (S Nb) k))). clear f.
change h with (comp (fun i => BABS (fun_of_matrix (col_maj diff) (inord i) ord0)) (@nat_of_ord (muln (S Nb) (S k)))). clear h.
replace g with (comp (fun i => BABS (diff (inord i) (Ordinal H))) (@nat_of_ord (S Nb))).
2:{
extensionality i; subst g; simpl. f_equal. unfold diff. 
rewrite mxE.
rewrite inord_val.
f_equal.
apply Fmodel_signal_eq.
}
clear g.
rewrite !map_ord_enum_inord.
set f := fun _ => _.
replace (map _ (iota 0 (S Nb))) with (map f (iota (muln (S Nb) k) (S Nb))).
rewrite -map_cat - iotaD. f_equal. f_equal. lia. subst f.
replace (iota (muln (S Nb) k) (S Nb)) with (iota (addn (muln (S Nb) k) 0) (S Nb)) by (f_equal; lia).
rewrite iotaDl.
rewrite -map_comp.
apply eq_in_map.
intros i H0.
rewrite mem_iota in H0. simpl in H0. replace (addn 0 (S Nb)) with (S Nb) in H0 by lia.
replace (inord i) with (Ordinal H0) by (apply ord_inj; rewrite inordK; auto).
rewrite /comp.
f_equal.
assert ( is_true (i + k * Nb.+1 < Nb.+1 * Nfr.+1)%N) by nia.
replace (inord (Nb.+1*k+i)) with (@Ordinal (S (Nfr + Nb * Nfr.+1))  _ H1)
  by (apply ord_inj; rewrite inordK; simpl; lia).
apply (col_majE diff (Ordinal H0) (Ordinal H) (Ordinal H1)); auto.
Qed.

Lemma OK_iterk: snd (Pmodel.iterk D waves Nfr.+1) = (Fmodel.energy_sum D, Fmodel.diff_sum D).
Proof.
unfold Pmodel.iterk.
unfold Fmodel.energy_sum, Fmodel.diff_sum.
fold Nfr. fold Nb.
rewrite OK_iterk_partial; [ | lia].
unfold snd.
do 2 f_equal; extensionality k; f_equal; f_equal; apply inord_val.
Qed.

Lemma REL_synth_err: Pmodel.synth_err D = Fmodel.result D.
Proof.
unfold Pmodel.synth_err, Fmodel.result.
fold Nfr.
pose proof OK_iterk.
fold waves.
destruct (Pmodel.iterk D waves Nfr.+1) as [? [? ?]].
inv H.
auto.
Qed.

End DATA.
End Pmodel_Fmodel.

