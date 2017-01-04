Require Import SetoidCat SetoidUtils Functor Applicative FoldableFunctor Monoid Algebra.Functor.Identity Algebra.Functor.Compose Algebra.Applicative.Identity Algebra.Applicative.Compose Algebra.Applicative.Transformation.

Require Import SetoidClass.

Section Traversable.

  Context
    {t tS} {func : @Functor t tS} .
  
  Existing Instance IdentityFunctor.
  Existing Instance IdentityS.
  Existing Instance Identity_Applicative.
  Existing Instance ComposeFunctor.
  Existing Instance ComposeS.
  Existing Instance Compose_Applicative.

  Class Traversable :=
    {
      sequenceA {t' tS'}
               {func' : @Functor t' tS'}
               {app' : @Applicative _ _ func'}
               {A} {AS : Setoid A} :
        tS _ (tS' _ AS) ~> tS' _ (tS _ AS);
      
      sequenceA_IdentityFunc :
        forall {A} {AS : Setoid A},
          sequenceA == IdentityIsoS _ ∘ fmap @ IdentityIsoS' _;
      
      sequenceA_ComposeFunc :
        forall {t'  t'' tS' tS''}
               {func' : @Functor t' tS'}
               {func'' : @Functor t'' tS''}
               {app' : @Applicative _ _ func'}
               {app'' : @Applicative _ _ func''}
               {A} {AS : Setoid A},
          sequenceA == @ComposeIsoS t' t'' _ _ _ _
                      ∘ fmap @ sequenceA ∘ sequenceA
                      ∘ fmap @ @ComposeIsoS' t' t'' _ _ _ _;

      sequenceA_naturality:
        forall {t'  t'' tS' tS''}
               {func' : @Functor t' tS'}
               {func'' : @Functor t'' tS''}
               {app' : @Applicative _ _ func'}
               {app'' : @Applicative _ _ func''}
               (tr : forall {A : Type} {AS : Setoid A}, tS' A AS ~> tS'' A AS)
               {A} {AS : Setoid A},
          ApplicativeTransformation (@tr) ->
        tr ∘ sequenceA == sequenceA ∘ (fmap @ tr)
    }.

End Traversable.
