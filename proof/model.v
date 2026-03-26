Require Import VST.floyd.functional_base.
From vcfloat Require Import FPStdCompCert FPStdLib.
From LAProof.C Require Import floatlib matrix_model.
Import Rdefinitions.

Record wave := {
   Wave_N: Z;
   Wave_A: list (ftype Tdouble);
   Wave_σ: list (ftype Tdouble);
   Wave_v: list (ftype Tdouble);
   Wave_θ0: ftype Tdouble;
   Wave_A_len: Zlength Wave_A = Wave_N;
   Wave_σ_len: Zlength Wave_A = Wave_N;
   Wave_v_len: Zlength Wave_A = Wave_N;
   Wave_t_len: Zlength Wave_A = Wave_N
}.

Record data := {
   Data_Nb: Z;
   Data_Nfr: Z;
   Data_Nbg: Z;
   Data_dt: ftype Tdouble;
   Data_XT : list (ftype Tdouble);
   Data_BG: list (ftype Tdouble);
   Data_waves: list wave;
   Data_Nb_pos: 0 < Data_Nb;
   Data_XT_len: Zlength Data_XT = (Data_Nfr * Data_Nb)%Z;
   Data_BG_len: Zlength Data_BG = (Data_Nbg * Data_Nb)%Z
}.

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

Definition L := BMULT (Zconst _ 2) M_PI.

Definition range2pi (x: ftype Tdouble) : ftype Tdouble :=
    BMINUS x (BMULT L (BFLOOR (BDIV x L))).

Definition wrap (x: ftype Tdouble) : ftype Tdouble :=
   BMINUS (range2pi (BPLUS x M_PI)) M_PI.

Definition interpolate (f: ftype Tdouble) (y: list (ftype Tdouble)) (k: ftype Tdouble) : ftype Tdouble :=
  let j := Binary.Btrunc _ _ (BFLOOR (BDIV k f)) in
  let frac := BDIV (BMINUS k (BMULT (Zconst _ j) f)) f in
   if  BCMP Gt true frac (Zconst _ 0) 
   then BPLUS (Znth j y) (BMULT frac (BMINUS (Znth (j+1) y) (Znth j y)))
   else Znth j y.


Fixpoint map2 [A B C] (f: A -> B -> C) (al: list A) (bl: list B) : list C :=
 match al, bl with
 | a::al', b::bl' => f a b :: map2 f al' bl'
 | _ , _ => nil
 end.

Definition map_upto [A] (k: Z) (f: Z -> A) := map f (upto (Z.to_nat k)).

Definition getBG (Nfr Nb: Z) (BG: list (ftype Tdouble)) (k: Z) : list (ftype Tdouble) :=
  let Nbg := (Zlength BG / Nb)%Z in 
  let f := Binary.Btrunc _ _ (BMULT (Zconst Tdouble k) (BDIV (Zconst Tdouble (Nbg-1)) (Zconst Tdouble (Nfr-1)))) in 
    sublist (f*Nb) ((f+1)*Nb) BG.

Require VSTlib.spec_math.

Definition Bexp : ftype Tdouble -> ftype Tdouble := FPCore.ff_func VSTlib.spec_math.MF.exp.

Definition waveform (Nb :Z) (A σ θ: ftype Tdouble)  (i: Z) : ftype Tdouble :=
   let dx := wrap (BMINUS (BMULT (Zconst Tdouble i) (BDIV L (Zconst _ Nb))) θ) in
     BMULT A (Bexp (BOPP (BDIV (BMULT dx dx) (BMULT (Zconst _ 2) (BMULT σ σ))))).

Definition getW (Nfr Nb: Z) (dt: ftype Tdouble) (k: Z)  (θw: ftype Tdouble * wave) : list (ftype Tdouble) :=
  let '(θ, w) := θw in
  let f := BDIV (Zconst Tdouble (Nfr-1)) (Zconst Tdouble (Nb-1)) in
  let A := interpolate f (Wave_A w) (Zconst _ k) in
  let σ := interpolate f (Wave_σ w) (Zconst _ k) in
  map_upto Nb (waveform Nb A σ θ).

Definition updateθ (Nfr: Z) (k: Z) (dt: ftype Tdouble) (θw: ftype Tdouble * wave) : ftype Tdouble * wave :=
 let '(θ, w) := θw in 
 let f := BDIV (Zconst Tdouble (Nfr-1)) (Zconst Tdouble (Zlength (Wave_A w)-1)) in
 let v := interpolate f (Wave_v w) (Zconst _ (k-1)) in
 (BPLUS θ (BMULT v dt), w).

Fixpoint iterk (Nfr Nb : Z) (dt: ftype Tdouble) (BG X: list (ftype Tdouble)) (k': nat) (θw: list (ftype Tdouble * wave)) (energy diff_sum: ftype Tdouble) : ftype Tdouble :=
 match k' with O => BDIV diff_sum energy
 | S k1 => 
 let k := (Nfr-Z.of_nat k')%Z in
 let e_bg := getBG Nfr Nb BG k in
 let θw' := if Z.eq_dec k 0 then θw else map (updateθ Nfr k dt) θw in
 let ew := map (getW Nfr Nb dt k) θw' in
 let e := fold_left (map2 BPLUS) ew e_bg in
 let Xk := sublist (k*Nb) ((k+1)*Nb) X in 
 let energy' := fold_left BPLUS (map BABS Xk) energy in
 let d' := fold_left BPLUS (map BABS (map2 BMINUS Xk e)) diff_sum in
 iterk Nfr Nb dt BG X k1 θw' energy' d'
 end.

Definition synth_err (d: data) : ftype Tdouble :=
 let '{| Data_Nb := Nb; Data_Nfr := Nfr; Data_Nbg := Nbg; Data_dt := dt; 
          Data_XT := XT; Data_BG := BG; Data_waves := waves;
          Data_Nb_pos := HNb; Data_XT_len := HXT; Data_BG_len := HBG |} := d in
   iterk Nfr Nb dt BG XT (Z.to_nat Nfr) (List.combine (map Wave_θ0 waves) waves) (Zconst  _ 0) (Zconst _ 0).
