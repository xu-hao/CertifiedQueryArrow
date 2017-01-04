Require Import   Algebra.SetoidCat Algebra.Monoid Algebra.NearSemiRing.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Section Instances.
  Context
    {A AS}
    (nsr : @NearSemiRing A AS).
  
  Instance nearSemiRing_times_Monoid : @Monoid A AS.
  Proof.
    exists (one) (times).
    apply times_left_unit.
    apply times_right_unit.
    apply times_associativity.
  Defined.
End Instances.
