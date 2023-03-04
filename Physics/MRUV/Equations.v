Set Implicit Arguments.
From mathcomp Require Import all_ssreflect.
Require Import Coq.Reals.Reals.
Require Import Lra.
Require Import Pruvaro.Physics.MRUV.Definition.

Local Open Scope R_scope.
(** * Torricelli's equation *)
(** One of the most well-known non-trivial results in
    constant acceleration systems is the Torricelli's
    equation, which relates velocities and positions
    without making explicit mention to time.
 *)


Theorem torricelli_equation (m : MRUV.model) :
  let: @MRUV.Pack x0 v0 a x v xAxm vAxm := m in
  let Δx : R -> R := fun t => (x t) - x0 in
  forall (t : R), (v t) ^ 2 = v0 ^ 2 + 2 * a * (Δx t).
Proof.
  case: m => x0 v0 a x v xAxm vAxm Δx.
  unfold MRUV.position_axiom in xAxm.
  unfold MRUV.velocity_axiom in vAxm.
  unfold Δx.
  move => t. rewrite vAxm xAxm. lra.
Qed.
