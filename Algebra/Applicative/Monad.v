Require Import  Algebra.SetoidCat SetoidUtils Algebra.Functor Algebra.Applicative Tactics Algebra.SetoidCat.PairUtils Algebra.Monad Algebra.Functor.Monad Algebra.Monad.Utils.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Open Scope type_scope.



Section Instances.

Existing Instance monadFunctor.
Instance monad_Applicative {m mS}{mnd : @Monad m mS} : @Applicative m mS _.
Proof.
  exists (ret @ tt) (@monad_prod m mS mnd ).
  intros. simpl. normalize_monad. rewrite right_unit_equiv. reflexivity. simpl. arrequiv. normalize_monad. reflexivity.
  intros. simpl. normalize_monad. rewrite right_unit_equiv. reflexivity. simpl. arrequiv. normalize_monad. reflexivity.
  intros. simpl. normalize_monad. bindproper. normalize_monad. bindproper. normalize_monad. bindproper. normalize_monad. reflexivity.
  intros. simpl. normalize_monad. bindproper. normalize_monad. bindproper. normalize_monad. reflexivity.
Defined.
End Instances.
