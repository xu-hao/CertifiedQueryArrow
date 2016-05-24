Require Import Maybe.
Require Import SetoidClass.
Class Pointed A : Type :=
  {
    point : A
  }
.


Instance nat_Pointed : Pointed nat :=
  {
    point := 0
  }.


Instance maybe_Pointed A : Pointed (option A) :=
  {
    point := None
  }.
