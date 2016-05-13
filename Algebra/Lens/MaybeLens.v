Require Import Algebra.Functor Algebra.Applicative Algebra.SetoidCat Algebra.PairUtils Algebra.SetoidUtils Algebra.Monad Tactics Utils Algebra.Lens.LensTypes Algebra.Maybe.
Require Import SetoidClass Vector.

Instance Some_Proper A (AS : Setoid A) : Proper (equiv ==> equiv) (@Some A).
Proof.
  autounfold. intros. simpl. auto.
Qed.

Definition SomeS {A} {AS : Setoid A} : AS ~> maybeS AS := injF Some _.

Definition _maybePrism' {A} {AS : Setoid A} : _Prism' (maybe A) A.
  unfold _Prism'. intros. refine (match X0 with
                                    | None => pure @ X0
                                    | Some a => SomeS <$> X @ a
                                  end).
Defined.

Definition _maybePrism {f fS func} {app : @Applicative f fS func} {A} {AS : Setoid A} :
  (AS ~> fS _ AS) -> maybe A -> f (maybe A) _ := _maybePrism' f fS func app.

Instance _maybePrism_Proper {f fS func} {app : @Applicative f fS func} A (AS : Setoid A) : Proper (equiv ==> equiv ==> equiv) (_maybePrism).
Proof.
  autounfold. intros. unfold _maybePrism, _maybePrism'. matchequiv. simpl in H0.  rewritesr.
Qed.

Definition maybePrism {f fS func} {app : @Applicative f fS func} {A} {AS : Setoid A} := injF2 _maybePrism _.
