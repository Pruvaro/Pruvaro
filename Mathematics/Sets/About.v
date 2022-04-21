(** * About: Sets *)

(** The Sets directory is a directory containing proofs of Set Theory.
    
    In the Coq Standard library, the idea of a set (as defined in ZFC) is
    encoded in the idea of an [Ensemble]. By definition, we have

    [Definition Ensemble (T : Type) := T -> Prop]

    That is, given a type, say, [nat], [Ensemble nat] is simply the type of all
    [Prop]-valued predicates over the natural numbers.

    The standard library has many theorems and definitions which deal with
    sets. However, they lack some, specially related with operations on
    infinite families. Therefore, the main goal of the Sets directory is
    to house proofs and definitions that extend the ones already provided
    in the standard library.
 *)
    
