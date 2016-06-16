Require Import SetoidClass SetoidCat.

Instance boolS : Setoid bool :=
  {
    equiv := eq
  }
.



Definition andbS : boolS ~> boolS ~~> boolS.
  simple refine (injF2 andb _).
Defined.

Definition negbS : boolS ~> boolS.
  simple refine (injF negb _).
Defined.

