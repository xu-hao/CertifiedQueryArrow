Require Import Algebra.Functor Algebra.Applicative Algebra.SetoidCat Algebra.ListUtils Algebra.PairUtils Algebra.Maybe Algebra.SetoidUtils Algebra.Monad  Tactics Utils VectorUtils.
Require Import SetoidClass List.


Definition _Prism' A B {AS : Setoid A} {BS : Setoid B} :=
  forall {f fS func} {app : @Applicative f fS func}, (BS ~> fS _ BS) -> (A -> f A _).

Definition Prism' A B {AS : Setoid A} {BS : Setoid B} :=
  forall {f fS func} {app : @Applicative f fS func}, (BS ~~> fS _ BS) ~> (AS ~~> fS _ AS).

Definition _Traversal' A B {AS : Setoid A} {BS : Setoid B} :=
  forall {f fS func} {app : @Applicative f fS func}, (BS ~> fS _ BS) -> (A -> f A _).

Definition Traversal' A B {AS : Setoid A} {BS : Setoid B} :=
  forall {f fS func} {app : @Applicative f fS func}, (BS ~~> fS _ BS) ~> (AS ~~> fS _ AS).

Definition _Iso' A B {AS : Setoid A} {BS : Setoid B} :=
  forall {f fS} {func : @Functor f fS}, (BS ~> fS _ BS) -> (A -> f A _).

Definition Iso' A B {AS : Setoid A} {BS : Setoid B} :=
  forall {f fS} {func : @Functor f fS}, (BS ~~> fS _ BS) ~> (AS ~~> fS _ AS).

Definition _Lens' A B {AS : Setoid A} {BS : Setoid B} :=
  forall {f fS} {func : @Functor f fS}, (BS ~> fS _ BS) -> (A -> f A _).

Definition Lens' A B {AS : Setoid A} {BS : Setoid B} :=
  forall {f fS} {func : @Functor f fS}, (BS ~~> fS _ BS) ~> (AS ~~> fS _ AS).



(* Definition ASetter' A B {AS : Setoid A} {BS : Setoid B} :=
  (BS ~~> IdentityS BS) ~> (AS ~~> IdentityS AS).

Definition Getting A B {AS : Setoid A} {BS : Setoid B} :=
  (BS ~~> ConstS BS BS) ~> (AS ~~> ConstS BS AS). *)
