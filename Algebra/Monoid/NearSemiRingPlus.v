Require Import   Algebra.SetoidCat Algebra.Monoid Algebra.NearSemiRing.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Section Instances.
  Context
    {A AS}
    (nsr : @NearSemiRing A AS).
  
  Instance nearSemiRing_plus_Monoid : @Monoid A AS.
  Proof.
    exists (zero) (plus).
    apply plus_left_unit.
    apply plus_right_unit.
    apply plus_associativity.
  Defined.
End Instances.
