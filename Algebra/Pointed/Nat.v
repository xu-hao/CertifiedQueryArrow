Require Import Algebra.SetoidCat.MaybeUtils SetoidCat Algebra.Pointed.
Require Import SetoidClass.


Instance nat_Pointed : Pointed nat :=
  {
    point := 0
  }.


