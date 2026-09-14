Set Implicit Arguments.
Set Universe Polymorphism.

(** Shared tagged input; independent of either parenthesis representation. *)
Inductive del (A D : Type) :=
| E : A -> del A D
| Del : D -> del A D.

Arguments E {_ _} _.
Arguments Del {_ _} _.
