Require Import Algebra.Monad.Utils Algebra.SetoidCat SetoidUtils Algebra.Functor Algebra.Applicative Tactics Algebra.SetoidCat.PairUtils Algebra.Monad.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Open Scope type_scope.



Section Instances.
Instance monadFunctor  {m mS} {mnd : @Monad m mS} : @Functor m mS.
Proof.
  exists (@monad_fmap m mS mnd).
  intros. simpl. arrequiv. normalize_monad. bindproper. simpl. arrequiv. unfold comp. rewrite left_unit. simpl. reflexivity.
  intros. simpl. arrequiv. rewrite right_unit_equiv. reflexivity. simpl. arrequiv.
Defined.

End Instances.
