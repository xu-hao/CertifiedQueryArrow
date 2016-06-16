Require Import SetoidClass.

Instance unitS : Setoid unit :=
  {
    equiv := eq
  }
.
