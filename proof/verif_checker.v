Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require Import spec_math spec_malloc.
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

Definition Gprog := [floor_spec; exp_spec; range2pi_spec; wrap_spec; synthesize_spec].

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

Lemma body_synthesize: semax_body Vprog Gprog f_synthesize synthesize_spec.
Admitted.


