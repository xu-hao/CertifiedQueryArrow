Require Import Algebra.SetoidCat.MaybeUtils SetoidCat.
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

Class PointedFunction2 {A B C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C} {AP :Pointed A} {BP :Pointed B} {CP : Pointed C} (f : AS ~> BS ~~> CS) :=
  {
    pointed2 : f @ point @ point == point
  }
.

Class PointedFunction {A B } {AS : Setoid A} {BS : Setoid B}  {AP :Pointed A} {BP :Pointed B}  (f : AS ~> BS) :=
  {
    pointed : f @ point  == point
  }
.
