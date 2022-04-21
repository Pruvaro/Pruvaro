(** See the associated page in the wiki: [TODO] *)
(** Axiom set: 

    * Extensionality_Ensembles 

 *)

(** * About
    This module provides the definitions for families of sets:
    both standard families (sets of sets) as well as indexed
    families. As standard in Coq, we use the word "set" to
    refer to [Ensemble]s.

    As well as providing the definitions for set families, we
    provide some definitions for family union and intersection.
 *)
From mathcomp Require Import all_ssreflect.
From Coq Require Export Sets.Classical_sets.
Require Export Pruvaro.Mathematics.Sets.EnsemblesNotations.
Set Implicit Arguments.

(** Open [set_scope] to get access to handy set notations. *)
Open Scope set_scope.

(** * Families *)
Section Families.

  (** A general type for all the Ensembles *)
  Variable (T : Type).

  (** Non-indexed families. *)
  Definition Family := Ensemble (Ensemble T).

  (** ** Family Unions *)

  (** An inductive definition for the union of a non-indexed family. *)
  Inductive FamilyUnion (F : Family) : Ensemble T :=
  | familyUnionIntro : forall (S : Ensemble T) (x : T),
      S ∈ F -> x ∈ S -> x ∈ FamilyUnion F.

  (** ** Family Intersection *)
  Inductive FamilyIntersection (F : Family) : Ensemble T :=
    | familyIntersectionIntro : forall (x : T),
      (forall (S : Ensemble T), S ∈ F -> x ∈ S) -> x ∈ (FamilyIntersection F).
End Families.

(** *** Arguments
    We set the type arguments of FamilyUnion and
    FamilyIntersection to implicit.
 *)
Arguments FamilyUnion {T}.
Arguments FamilyIntersection {T}.

(** *** Notation 
    We will add two notations for the intersection and union of 
    non-indexed families one inspired by LaTeX, and another one 
    using UTF8.
*)

(** LaTeX inspired *)
Notation "'bigcup' F" := (FamilyUnion F)
(only parsing, at level 0) : set_scope.
(** printing \bigcup $\bigcup$ #⋃# *)

Notation "'bigcap' F" := (FamilyIntersection F)
(only parsing, at level 0) : set_scope.
(** printing \bigcap $\bigcap$ #⋂# *)

(** UTF8 *)
Notation "'⋃' F" := (FamilyUnion F)
(at level 0) : set_scope.
(** printing ⋃ $\bigcup$ #⋃# *)

Notation "'⋂' F" := (FamilyIntersection F)
(at level 0) : set_scope.
(** printing ⋂ $\bigcap$ #⋂# *)

(** * Indexed families *)
Section IndexedFamilies.

  Variable (A T : Type).
  Definition IndexedFamily := A -> Ensemble T.
      
  (** ** Indexed family union *)
  Inductive IndexedUnion (F : IndexedFamily) : Ensemble T :=
    | indexedUnionIntro : forall (a : A) (x : T),
        x ∈ (F a) -> x ∈ (IndexedUnion F).

  (** ** Indexed family intersection *)
  Inductive IndexedIntersection (F : IndexedFamily) : Ensemble T :=
    | indexedIntersectionIntro : forall (x : T),
        (forall (a : A), x ∈ (F a)) -> x ∈ (IndexedIntersection F).

End IndexedFamilies.

(** *** Arguments
    We set the type arguments of IndexedUnion and IndexedIntersection
    as implicit.
 *)
Arguments IndexedUnion {A T}.
Arguments IndexedIntersection {A T}.

(** *** Notation 
    We will add two notations for the union of non-indexed families: one
    inspired by LaTeX, and another one using UTF8.
*)
(** LaTeX inspired *)
Notation "'bigcup_' ( a : A ) F" := (IndexedUnion (fun (a : A) => F))
  (only parsing, at level 0, a at level 99 as name, A at level 200)
  : set_scope.

Notation "'bigcap_' ( a : A ) F" := (IndexedIntersection (fun (a : A) => F))
  (only parsing, at level 0, a at level 99 as name, A at level 200)
  : set_scope.

(** UTF8 *)
Notation "'⋃_' ( a : A ) F" := (IndexedUnion (fun (a : A) => F))
  (at level 0, a at level 99 as name, A at level 200)
  : set_scope.

Notation "'⋂_' ( a : A ) F" := (IndexedIntersection (fun (a : A) => F))
  (at level 0, a at level 99 as name, A at level 200)
  : set_scope.

(** * Hints *)
#[global]
Hint Unfold Family IndexedFamily : sets.

#[global]
Hint Resolve familyUnionIntro familyIntersectionIntro indexedUnionIntro
  indexedIntersectionIntro : sets.


(** * Family facts 
    
    In this section, we derive some basic lemmas about non-indexed families.
 *)
Section FamilyFacts.
  Variable (T : Type).

  (** The union of the empty family is the empty set. *)
  Lemma emptyFamilyUnion :
    ⋃ (@Empty_set (Ensemble T)) = ∅.
  Proof using Type.
    apply Extensionality_Ensembles. unfold Same_set. split; unfold Included.
      move => x [S x0 [] _].
    move => x [].
  Qed.

  (** The intersection of the empty family is the full set. *)
  Lemma emptyFamilyIntersection :
    ⋂ (@Empty_set (Ensemble T)) = Full_set.
  Proof using Type.
    apply Extensionality_Ensembles. unfold Same_set. split; unfold Included.
      by move => x [x0 _].
    move => x _. unfold In. constructor => S [].
  Qed.

  (** The union of a subfamily is contained in the union of the
      larger family.
   *)
  Lemma subfamilyUnion :
    forall (F G : Family T), F ⊆ G -> ⋃ F ⊆ ⋃ G.
  Proof using Type.
    move => F G. unfold Included => hInF_InG x [S x0 hSinF hxInS].
    apply familyUnionIntro with S; by [ | apply: hInF_InG hSinF].
  Qed.

  (** The intersection of a subfamily contains the intersection
      of the larger family.
   *)
  Lemma subfamilyIntersection :
    forall (F G : Family T), F ⊆ G -> ⋂ G ⊆ ⋂ F.
  Proof using Type.
    move => F G. unfold Included => hInF_InG x [x0 hxInS].
    constructor => S hSinF. apply: hxInS. by apply: hInF_InG. 
  Qed.

  (** Complement of union is the intersection of complements. *)
  Lemma complementFamilyUnion :
    forall (F : Family T), Complement (⋃ F) = ⋂ ([[ S : Ensemble T | Complement S ∈ F ]]).
  Proof using Type.
    move => F. apply Extensionality_Ensembles. split; unfold Included.
    - unfold Complement => x hxInComp. unfold In in hxInComp.
      constructor => S hS. unfold In in hS.
      rewrite -[S in _ ∈ S]Complement_Complement. (* Notice the LEM. *)
      unfold In. unfold Complement. unfold In. intro hNotSx. apply hxInComp.
      by apply familyUnionIntro with (Complement S).
    - move => _ [x hxInAll] hxInUF.
      elim hEqxx': x /hxInUF => [S0 x' hS0InF hxInS]; subst x'.
      rewrite -[S0]Complement_Complement in hS0InF.
      by apply (hxInAll (Complement S0)) in hS0InF.
  Qed.

  (** Complement of intersection is the union of complements. *)
  Lemma complementFamilyIntersection :
    forall (F : Family T), Complement (⋂ F) = ⋃ ([[ S : Ensemble T | Complement S ∈ F ]]).
  Proof using Type.
    move => F. have compEq:
      forall (A B : Ensemble T), Complement A = Complement B -> A = B.
      - move => A B hEqCACB.
        rewrite -[A]Complement_Complement -[B]Complement_Complement.
        by rewrite hEqCACB.
      - apply: compEq. rewrite Complement_Complement complementFamilyUnion.
        unfold In. apply Extensionality_Ensembles. split;
        unfold Included => _ [x hxInAll]; constructor => S hS.
      - unfold In in hS. rewrite Complement_Complement in hS.
        by apply hxInAll.
      - apply hxInAll. unfold In. by rewrite Complement_Complement.
  Qed.

  (** The binary operator union is just the union of a couple family. *)  
  (* Lemma unionAsFamilyUnion :
     forall (A B : Ensemble T), A ∪ B = ⋃ (Couple A B).
  Proof.
    move => A B. apply Extensionality_Ensembles; split; unfold Included; move => x.
    - move => hxInAUB. unfold In in hxInAUB. case hxInAUB.
      - move => x0 hx0InA. apply familyUnionIntro with A.
        - unfold In. constructor.
        - by [].
      - move => x0 hx0InB. apply familyUnionIntro with B.
        - unfold In. constructor.
        - by [].
      - move => [C x' hCInAB hxInC].
        constructor in hCInAB.
  *)
  
End FamilyFacts.
  
      
    
