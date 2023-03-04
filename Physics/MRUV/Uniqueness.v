Set Implicit Arguments.
From mathcomp Require Import all_ssreflect.
Require Import Coq.Reals.Reals.
Require Import Lra.
Require Import Pruvaro.Physics.MRUV.Definition.

Local Open Scope R_scope.
(** * Unicidade  *)
Section Uniqueness.
 (** Nesse arquivo, provaremos alguns resultados a respeito da unicidade
      dos modelos em MRUV. Por exemplo, provaremos que o valor da posição
      inicial, da velocidade inicial, e da aceleração definem unívocamente
      uma instância de um modelo MRUV, isto é, quaisquer dois modelos com
      os mesmos valores iniciais descreverão a mesma dinâmica, sendo
      então equivalentes ao considerar a relação [MRUV.equiv].

      Ao final, congregando todos esses resultados, provaremos uma versão
      formal do Demônio de Laplace para o MRUV.
  *)

  (** Em primeiro lugar, definiremos uma função que gera uma instância de
      modelo MRUV dados três valores que corresponderão às condições
      iniciais e à aceleração.

      Para tanto, definimos uma função que produz a função posição, e
      outra que produz a função velocidade.
   *)
  Definition xFromInit (x0 v0 a : R) : R -> R :=
    fun t => x0 + v0 * t + 0.5 * a * (t ^ 2).

  Definition vFromInit (v0 a : R) : R -> R :=
    fun t => v0 + a * t.

  (** Agora, definimos teoremas que provam que essas funçõs produzem
      funções que satisfazem os axiomas.
   *)
  Lemma xFromInit_correct (x0 v0 a : R) :
    MRUV.position_axiom x0 v0 a (xFromInit x0 v0 a).
  Proof.
    by [].
  Qed.

  Lemma vFromInit_correct (v0 a : R) :
    MRUV.velocity_axiom v0 a (vFromInit v0 a).
  Proof.
    by [].
  Qed.


  (** Com esses teoremas certificando nossas funções, podemos construir
      a função que produz uma instância completa de modelo de MRUV.
   *)
  Definition mruvFromInit (x0 v0 a : R) : MRUV.model :=
    let x := xFromInit x0 v0 a in
    let v := vFromInit    v0 a in
    let xAxm := xFromInit_correct x0 v0 a in
    let vAxm := vFromInit_correct    v0 a in
    @MRUV.Pack x0 v0 a x v xAxm vAxm.

  (** Definimos agora um predicado que pode ser lido "as condições iniciais
      do modelo [m] são [x0] e [v0]" e sua aceleração é [a].
   *)
  Definition modelCond (x0 v0 a : R) (m : MRUV.model) : Prop :=
    (MRUV.x0 m = x0) /\ (MRUV.v0 m = v0) /\ (MRUV.a m = a).
  
  (** Demônio de #<s>La+</s> Laplace *)
  Theorem laplaceDemon (x0 v0 a : R) :
    exists (m : MRUV.model),
      (modelCond x0 v0 a m)
      /\ (forall (m' : MRUV.model), modelCond x0 v0 a m' -> MRUV.equiv m m').
  Proof.
    exists (mruvFromInit x0 v0 a). split. by [].
    move => [x0' v0' a' x' v' xAxm' vAxm'] [/= Hx0' [Hv0' Ha']].
    unfold MRUV.equiv. split.
    - have -> : MRUV.x (MRUV.Pack xAxm' vAxm') = x'. by [].
      simpl. unfold xFromInit. unfold MRUV.position_axiom in *.
      by rewrite xAxm' Hx0' Hv0' Ha'.
    have -> : MRUV.v (MRUV.Pack xAxm' vAxm') = v'. by []. 
    simpl. unfold vFromInit. unfold MRUV.velocity_axiom in *.
    by rewrite vAxm' Hv0' Ha'.
  Qed.

  About laplaceDemon.

End Uniqueness.


