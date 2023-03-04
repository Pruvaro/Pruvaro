Set Implicit Arguments.
Require Import Coq.Reals.Reals.

(** Lorem ipsum dolor sit amet, consectetur adipiscing elit. 
    Nam eget libero fermentum, dapibus mi quis, vestibulum 
    nisi. Praesent in fermentum urna, id fermentum enim. 

    Nullam mollis facilisis porttitor. Fusce tincidunt non 
    elit ac aliquet. Fusce in leo aliquam, convallis tortor 
    in, commodo erat. Morbi sed nisi eu nisi faucibus 
    lacinia. Suspendisse potenti. In tempus metus nisi, 
    sit amet euismod turpis vulputate vel. 
 *)

Theorem modus_ponens :
  forall (P Q : Prop), P -> (P -> Q) -> Q.
Proof.
  intros P Q.
  intros hP hPimpQ.
  apply hPimpQ.
  apply hP.
Qed.
