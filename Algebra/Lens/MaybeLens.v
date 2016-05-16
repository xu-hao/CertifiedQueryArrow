Require Import Algebra.Functor Algebra.Applicative Algebra.SetoidCat Algebra.PairUtils Algebra.SetoidUtils Algebra.Monad Tactics Utils Algebra.Lens.LensTypes Algebra.Maybe Lens.
Require Import SetoidClass Vector.


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




Lemma maybePrism_comp_preview:
  forall (A : Type) (AS : Setoid A)
       B (BS : Setoid B) (l : (BS ~~> ConstS (maybeS BS) BS) ~> AS ~~> ConstS (maybeS BS) AS),
    previewS @ (maybePrism ∘ l) == previewS @ maybePrism >=> previewS @ l.
Proof.
  intros. simpl_equiv.  Opaque equiv. simpl. unfold _maybePrism, _maybePrism', _pre0. destruct a.
  - simpl. reflexivity.
  - simpl. reflexivity. 
Qed.


Lemma maybePrism_comp_set:
  forall (A : Type) (AS : Setoid A)
       B (BS : Setoid B) (l : (BS ~~> IdentityS BS) ~> AS ~~> IdentityS AS) b h,
    set (maybePrism ∘ l) @ b @ h == caseMaybeS
                                      @ (flipS @ set maybePrism @ h ∘ set l @ b)
                                      @ h
                                      @ (previewS @ maybePrism @ h).
Proof.
  intros. destruct h.
  - simpl. reflexivity.
  - simpl. reflexivity. 
Qed.
