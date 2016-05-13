Require Import Algebra.Functor Algebra.Applicative Algebra.SetoidCat Algebra.SetoidUtils Algebra.PairUtils Algebra.SetoidUtils Algebra.Monad Tactics Utils Algebra.Lens.LensTypes Algebra.Maybe.
Require Import SetoidClass Vector.

Definition _fstLens' {A} {B} {AS : Setoid A} {BS : Setoid B} : _Lens' (A * B) A.
  unfold _Lens'. intros. refine (flipS @ pairS @ (sndS @ X0) <$> X @ (fstS @ X0)).
Defined.

Definition _fstLens {f fS} {func : @Functor f fS}  {A} {B} {AS : Setoid A} {BS : Setoid B} : (AS ~> fS _ AS) -> A * B -> f (A * B) _ := @_fstLens' A B _ _ f fS func.

Instance _fstLens_Proper {f fS} {func : @Functor f fS}  {A} {B} {AS : Setoid A} {BS : Setoid B} : Proper (equiv ==> equiv ==> equiv) (@_fstLens f fS func A B _ _).
Proof.
  autounfold. intros. unfold _fstLens, _fstLens'. rewritesr. 
Qed.

Definition fstLens {f fS} {func : @Functor f fS}  {A} {B} {AS : Setoid A} {BS : Setoid B} := injF2 (@_fstLens f fS func A B _ _) _.

Definition _sndLens' {A} {B} {AS : Setoid A} {BS : Setoid B} : _Lens' (A * B) B.
  unfold _Lens'. intros. refine (pairS @ (fstS @ X0) <$> X @ (sndS @ X0)).
Defined.

Definition _sndLens {f fS} {func : @Functor f fS}  {A} {B} {AS : Setoid A} {BS : Setoid B} : (BS ~> fS _ BS) -> A * B -> f (A * B) _ := @_sndLens' A B _ _ f fS func .

Instance _sndLens_Proper {f fS} {func : @Functor f fS}  {A} {B} {AS : Setoid A} {BS : Setoid B} : Proper (equiv ==> equiv ==> equiv) (@_sndLens f fS func  A B _ _).
Proof.
  autounfold. intros. unfold _sndLens, _sndLens'. rewritesr. 
Qed.

Definition sndLens {f fS} {func : @Functor f fS}  {A} {B} {AS : Setoid A} {BS : Setoid B} := injF2 (@_sndLens f fS func A B _ _) _.


        