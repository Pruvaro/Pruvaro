(** See the associated page in the wiki: [TODO] *)
(** Axiom set: Core *)

(** * About
    The goal of this module is to provide some ease-of-use for
    some definitions provided in the Coq Standard library for
    Ensembles by making some arguments implicit. 

    For example, the definition of [In],

    [In : forall (U : Type), Ensemble U -> U -> Prop]

    is not implicit on the type [U], which does not allow us to
    write [In x S] to say "the element [x] is in the set [S]".
 *)
From Coq Require Export Ensembles.

Arguments Add {U}.
Arguments Complement {U}.
Arguments Couple {U}.
Arguments Disjoint {U}.
Arguments Empty_set {U}.
Arguments Extensionality_Ensembles {U}.
Arguments Full_set {U}.
Arguments In {U}.
Arguments Included {U}.
Arguments Inhabited {U}.
Arguments Intersection {U}.
Arguments Setminus {U}.
Arguments Singleton {U}.
Arguments Strict_Included {U}.
Arguments Subtract {U}.
Arguments Triple {U}.
Arguments Union {U}.

Global Hint Constructors Full_set : sets.
