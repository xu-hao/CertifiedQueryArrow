Require Import SetoidCat SetoidUtils Functor Monoid PairUtils UnitUtils Algebra.Applicative.

Require Import SetoidClass.

Class ApplicativeTransformation  {t t' tS tS'} {func : @Functor t tS} {app' : @Applicative t tS func} {func' : @Functor t' tS'} {app': @Applicative t' tS' func'}
        (tr : forall {A} {AS : Setoid A}, tS _ AS ~> tS' _ AS) :=
  {
    app_trans_unit : tr @ unitA == unitA;
    app_trans_prod : forall {A B} {AS : Setoid A} {BS : Setoid B} (a : t A _)(b : t B _), tr @ (a ** b) == (tr @ a) ** (tr @ b);
    app_trans_naturality : forall {A B} {AS : Setoid A} {BS : Setoid B} (a : t A _) (f: AS ~> BS), tr @ (f <$> a) == f <$> tr @ a;
  }.

