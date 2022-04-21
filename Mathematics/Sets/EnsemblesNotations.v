(** See the associated page in the wiki: [TODO] *)
(** Axiom set: Core *)

(** * About
    
    The goal of this module is to provide some better notations
    for things already defined in the Coq Standard Library for
    dealing with [Ensembles]. These notations will be put in a
    scope called [set_scope].
 *)
Require Export Pruvaro.Mathematics.Sets.EnsemblesImplicit.

Declare Scope set_scope.

(** * Notations
   
    For most things, two notations will be provided: one
    being a LaTeX-inspired notation, and the other one
    being a UTF8 notation. Associated with each notation,
    we also add a pretty-printing directive for coqdoc.
 *)

(** ** Element membership 

    Here we do not define a LaTeX inspired notation since it clashes
    with ssreflect.
 *)
(** UTF8 *)
Notation "x ∈ S" := (In S x)
  (at level 75) : set_scope.
(** printing ∈ $\in$ #∈# *)


(** ** Set intersection *)

(** LaTeX inspired *)
Notation "S \cap T" := (Intersection S T)
  (right associativity, only parsing, at level 55) : set_scope.
(** printing \cap $\cap$ #∩# *)

(** UTF8 *)
Notation "S ∩ T" := (Intersection S T)
  (right associativity, only parsing, at level 55) : set_scope.
(** printing ∩ $\cap$ #∩# *)

(** ** Set union *)

(** LaTeX inspired *)
Notation "S \cup T" := (Union S T)
  (right associativity, only parsing, at level 65) : set_scope.
(** printing \cup $\cup$ #∪# *)

(** UTF8 *)
Notation "S ∪ T" := (Union S T)
  (right associativity, at level 65) : set_scope.
(** printing ∪ $\cup$ #∪# *)

(** ** Set subtraction *)

(** Simple notation *)
Notation "S \ T" := (Setminus S T)
  (no associativity, only parsing, at level 65) : set_scope.
(** printing \ $∖$ #∖# *)

(** LaTeX inspired *)
Notation "S \setminus T" := (Setminus S T)
  (no associativity, only parsing, at level 65) : set_scope.
(** printing \setminus $∖$ #∖# *)

(** UTF8 *)
Notation "S ∖ T" := (Setminus S T)
  (no associativity, at level 65) : set_scope.
(** printing ∖ $∖$ #∖# *)

(** ** Set inclusion *)
(** For set inclusion, we will opt to standardize it to ⊆ for
    the HTML notation, as well as using <<\subseteq>> for
    subset notation, since [⊂] and <<\subset>> is often
    ambiguous as to allowing for set equality or not.

    For proper set inclusion (that is, not allowing for set equality)
    see the #<a href="##Strict_set_inclusion" >Strict set inclusion</a>#
    section instead.
 *)

(** LaTeX inspired *)
Notation "S \subseteq T" := (Included S T)
  (at level 70, only parsing) : set_scope.
(** printing \subseteq $\subseteq$ #⊆# *)

(** UTF8 *)
Notation "S ⊆ T" := (Included S T)
  (at level 70) : set_scope.
(** printing \subseteq $\subseteq$ #⊆# *)

(** ** Strict set inclusion *)

(** LaTeX inspired *)
Notation "S \subsetneq T" := (Strict_Included S T)
  (at level 70, only parsing) : set_scope.
(** printing \subsetneq $\subsetneq$ #⊊# *)

(** UTF8 *)
Notation "S ⊊ T" := (Strict_Included S T)
  (at level 70) : set_scope.
(** printing ⊊ $\subsetneq$ #⊊# *)

(** * Empty set *)

(** LaTeX inspired *)
Notation "\emptyset" := Empty_set
  (at level 0, only parsing)
  : set_scope.
(** printing \emptyset $\emptyset$ #∅# *)

Notation "∅" := Empty_set
  (at level 0)
  : set_scope.
(** printing ∅ $\emptyset$ #∅# *)


(** * Singleton, couple, and triple sets *)

(** Singleton sets *)
Notation "[[ x ]]" := (Singleton x) (at level 0) : set_scope.

(** Couple sets *)
Notation "[[ x , y ]]" := (Couple x y) (at level 0) : set_scope.

(** Triple sets *)
Notation "[[ x , y , z ]]" := (Triple x y z) (at level 0) : set_scope.


(** * Set comprehension *)
(** We define a simpler notation for writing sets based on some property. *)
(** We also add notation for easily defining non-indexed families *)
Notation "[[ x : X | P ]]" := (fun (x : X) => P)
  (at level 0, x at level 99 as name, X at level 200, P at level 200)
  : set_scope.

