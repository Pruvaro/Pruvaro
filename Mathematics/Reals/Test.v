Set Implicit Arguments.
From mathcomp Require Import all_ssreflect.
Require Import Coq.Reals.Rdefinitions Coq.Reals.Raxioms.
Require Import Lra.

(** * About *)
(** The goal of this file is very simple: to understand how to start using
    real numbers in Coq proofs.

    Hopefully, in the future, this file will seem silly, since it will be
    obvious how to do it. However, currently, while looking at the standard
    library documentation, I am faced with three definitions of the real
    numbers: "Classical Reals", "Abstract Constructive Reals", and
    "Constructive Cauchy Reals", the last two deemed experimental.

    This suggests I should use the classical reals. However, there are a lot
    of different modules, and I am not really sure which one to import in
    order to get access to the real number type (if there even is such a thing)
    and I also not sure which module contains which properties.

    With this quick introduction, let us go into this discovery adventure.

    Our first goal will be to prove a very basic theorem: zero times any real
    number is zero. This should provide us insights to the notations for
    real numbers (how zero is represented, how the multiplication is 
    represented, and how equality is represented), as well as force us to learn
    some proof techniques applicable to real numbers. It should not be very
    difficult to prove (hopefully).
 *)
Local Open Scope R_scope.

Theorem Rplus_cancel_r :
  forall (x y z : R), x = y <-> x + z = y + z.
Proof.
  split.
    by move => ->.
  move => HEq. rewrite -[x in LHS]Rplus_0_l. rewrite -(Rplus_opp_r z).
  by rewrite Rplus_comm -Rplus_assoc HEq Rplus_assoc Rplus_opp_r Rplus_comm Rplus_0_l.
Qed.

  

Theorem mult_r0 (r : R) :
  r * 0 = 0.
Proof.
  rewrite -[r * 0 in LHS]Rplus_0_l -{1}(Rplus_opp_r (r * 0)).
  rewrite Rplus_assoc [e in r * 0 + e]Rplus_comm -Rplus_assoc.
  rewrite (Rplus_cancel_r _ _ (r * 0)).
  rewrite Rplus_assoc [e in r * 0 + _ + e]Rplus_comm Rplus_opp_r.
  rewrite [in LHS]Rplus_comm 2!Rplus_0_l.
  rewrite -Rmult_plus_distr_l.
  by rewrite Rplus_0_l.
Qed.

Theorem mult_neg1 (r : R) :
  r * - 1 = - r.
Proof.
  rewrite (Rplus_cancel_r _ _ (r * 1)) [in LHS]Rplus_comm [in RHS]Rplus_comm.
  rewrite [in RHS]Rmult_comm Rmult_1_l.
  rewrite -Rmult_plus_distr_l.
  rewrite 2!Rplus_opp_r.
  apply mult_r0.
Qed.

Theorem Rplus_0_l' :
  forall (r : R), r + 0 = r.
Proof.
  move => r. lra.
Qed.

(** Here I discovered [lra], the Real number equivalent of [lia] (the [i] in
    [lia] standing for "integers". I also discovered the tactic [lqa], the
    equivalent for rational numbers. They all have their own [Require Import]
    module, [Lia] for [lia], [Lqa] for [lqa], and [Lra] for [lra].

    I think [lra] stands for "Linear Real Arithmetic", which suggests the kind
    of things it can solve. As you can see, it solves the [mult_r0] theorem
    automatically, avoiding those four lines of rewrites.
 *)
Theorem mult_r0' (r : R) :
  r * 0 = 0.
Proof.
  lra.
Qed.
