Require Import Algebra.SetoidCat.MaybeUtils SetoidCat Algebra.Pointed.
Require Import SetoidClass.


Instance maybe_Pointed A : Pointed (option A) :=
  {
    point := None
  }.

