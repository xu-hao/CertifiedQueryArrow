Require Import SetoidCat SetoidUtils Algebra.Functor Algebra.Monoid PairUtils Algebra.Utils UnitUtils Algebra.Applicative Algebra.Applicative.Transformation.

Require Import SetoidClass.

Lemma app_trans_pure : forall {t t' tS tS'} {func : @Functor t tS} {func' : @Functor t' tS'} {app' : @Applicative t tS func}  {app': @Applicative t' tS' func'} {A} {AS : Setoid A}
                              (tr : forall {A} {AS : Setoid A}, tS _ AS ~> tS' _ AS),
                         ApplicativeTransformation (@tr) -> forall (a: A),
                         tr @ (pure @ a) == pure @ a.
Proof.
  intros. unfold pure. unfold flipS. normalizecomp. rewrite (app_trans_naturality). rewrite app_trans_unit. reflexivity.
Qed.

Lemma app_trans_ap : forall {t t' tS tS'} {func : @Functor t tS} {func' : @Functor t' tS'} {app' : @Applicative t tS func} {app': @Applicative t' tS' func'} {A B} {AS : Setoid A} {BS : Setoid B}
                            (tr : forall {A} {AS : Setoid A}, tS _ AS ~> tS' _ AS),
                       ApplicativeTransformation (@tr) -> forall (a: t A _) (f : t (AS ~> BS) _),
                                                            tr @ (f <*> a) == tr @ f <*> tr @ a.
Proof.
  intros. unfold ap. unfold comp2S. normalize. rewrite app_trans_naturality. rewrite app_trans_prod. reflexivity.
Qed.
