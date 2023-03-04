Set Implicit Arguments.
From mathcomp Require Import all_ssreflect.
Require Import Coq.Reals.Reals.
Require Import Lra.
Require Import Coq.Relations.Relations.

Declare Scope MRUV_scope.

Local Open Scope R_scope.

Module MRUV.

  Section MRUV_Axioms.

  Variable (x0 v0 a : R).

  Definition position_axiom (x : R -> R) : Prop :=
    forall (t : R), x t = x0 + v0 * t + 0.5 * a * (t ^ 2).

  Definition velocity_axiom (v : R -> R) : Prop :=
    forall (t : R), v t = v0 + a * t.

  End MRUV_Axioms.

  About position_axiom.

  Section MRUV_definition.

  Structure model :=
    Pack
    { x0 : R
    ; v0 : R   
    ; a  : R
    ; x  : R -> R
    ; v  : R -> R
    ; _  : position_axiom x0 v0 a x
    ; _  : velocity_axiom v0 a v
    }.

  End MRUV_definition.

  About x0.

  Section MRUV_equiv.

  Definition equiv (m1 m2 : MRUV.model) : Prop :=
    let x1 := x m1 in
    let v1 := v m1 in
    let x2 := x m2 in
    let v2 := v m2 in
      forall (t : R), (x1 t = x2 t) /\ (v1 t = v2 t).


  Theorem equiv_rel :
    equivalence model equiv.
  Proof.
    apply Build_equivalence.
    - (* reflexivity *)
      unfold reflexive. move => m. by unfold equiv.
    - (* transitivity *)
      unfold transitive. move => m1 m2 m3. unfold equiv.
      move => Hequiv12 Hequiv23 t.
      by case: (Hequiv12 t) => -> ->.
    - (* symmetry *)
      unfold symmetric. move => m1 m2. unfold equiv.
      move => Hequiv12 t. by case (Hequiv12 t) => -> ->.
  Qed.
    
  End MRUV_equiv.

End MRUV.

Notation "m1 ~=~ m2" := (equiv m1 m2) (at level 50) : MRUV_scope.
