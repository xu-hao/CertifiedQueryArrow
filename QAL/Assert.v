Require Import Coq.Program.Basics.

Require Import Tactics Algebra.Utils SetoidUtils Algebra.SetoidCat Algebra.SetoidCat.ListUtils Algebra.Monad Algebra.SetoidCat.PairUtils Algebra.SetoidCat.MaybeUtils Algebra.Monad.Maybe QAL.Definitions QAL.Command QAL.AbstractHeap QAL.AbstractStore.

Require Import FMapWeakList Coq.Lists.List RelationClasses Relation_Definitions Morphisms SetoidClass.


Section Assert.
  Context
    {builtin : Type}.

  Inductive assertion :=
  | emp : assertion
  | primitive : builtin -> assertion
  | sepConj : assertion -> assertion -> assertion
  | sepImp : assertion -> assertion -> assertion
  | atrue : assertion
  | aAnd : assertion -> assertion -> assertion
  | aNot : assertion -> assertion
  | aExists : var -> assertion -> assertion
  .

  Program Instance assertionS : Setoid assertion.


End Assert.

  Notation "a ∧ b" := (aAnd a b) (left associativity, at level 81).
  Notation "¬ a" := (aNot a) (at level 80).
(*  Notation "[[ addr , p ]] ⟼ val" := (singleton addr p val) (at level 79). *)
  Notation "a ∗ b" := (sepConj a b) (left associativity, at level 83).
  Notation "a -∗ b" := (sepImp a b) (right associativity, at level 84).
  Notation "∃ v , a" := (aExists v a) (at level 85).
  Notation "⊤" := (atrue) (at level 85).

  Module Type PrimitiveAssertion (PT : PredType) (VT : ValType) (S : AbstractStore VT) (H : AbstractHeap PT VT).
    Parameter primitiveAssertion : Type.
    Parameter primitiveAssertionS : Setoid primitiveAssertion.
    Parameter interpretPrimitiveAssertion : primitiveAssertionS ~> S.tS ~~> H.tS ~~> iff_setoid.
  End PrimitiveAssertion.
  
  Module AssertModel  (PT : PredType) (VT : ValType) (S : AbstractStore VT) (H : AbstractHeap PT VT) (PA: PrimitiveAssertion PT VT S H).
  Import S H PA.
  Definition assertion := @assertion primitiveAssertion.
  Instance assertionS : Setoid assertion := @assertionS primitiveAssertion.

  Fixpoint _models (a : assertion) (s : S.t) (h : H.t) {struct a} : Prop :=
    match a with
      | emp => isEmpty @ h
      | primitive pa => interpretPrimitiveAssertion @ pa @ s @ h
      | a0 ∗ a1 => exists h0 h1,
                     h0 ⊥ h1 /\ h0 ⋅ h1 == h /\ _models a0 s h0  /\ _models a1 s h1
      | a0 -∗ a1 => forall h',
                      h ⊥ h' -> _models a0 s h' -> _models a1 s (h ⋅ h') 
      | ¬ a => ~ _models a s h
      | a0 ∧ a1 => _models a0 s h /\ _models a1 s h
      | ⊤ => True
      | ∃ v, a => exists val, _models a (S.update @ v @ val @ s) h
    end.

  Definition models : assertionS ~> S.tS ~~> H.tS ~~> iff_setoid.
    simple refine (injF3 _models _).
    Lemma models_1 : Proper (equiv ==> equiv ==> equiv ==> equiv) _models.
    Proof.
      autounfold. intros x y H. rewrite H. clear x H. induction y.
      intros. unfold _models.  rewritesr. 
      intros. unfold _models. rewritesr.
      intros. simpl. split.
      intros. destruct H1. destruct H1. exists x1. exists x2. rewrite <- (IHy1 x y H x1 x1 (reflexivity x1)) , <- (IHy2 x y H x2 x2 (reflexivity x2)). rewrite <- H0. auto. 
      intros. destruct H1. destruct H1. exists x1. exists x2. rewrite (IHy1 x y H x1 x1 (reflexivity x1)) , (IHy2 x y H x2 x2 (reflexivity x2)). rewrite H0. auto. 
      intros. unfold _models. fold _models. split.
      intros. rewrite <- (IHy2 _ _ H (x0 ⋅ h') (y0 ⋅ h')). apply H1. rewrite H0. auto. rewrite (IHy1 _ _ H h' h'). auto. reflexivity. rewrite H0. reflexivity.
      intros. rewrite (IHy2 _ _ H (x0 ⋅ h') (y0 ⋅ h')). apply H1. rewrite <- H0. auto. rewrite <- (IHy1 _ _ H h' h'). auto. reflexivity. rewrite H0. reflexivity.
      intros. simpl. tauto.
      intros. simpl. rewrite (IHy1 _ _ H _ _ H0), (IHy2 _ _ H _ _ H0). tauto.
      intros. simpl. rewrite (IHy _ _ H _ _ H0). tauto.
      intros. simpl. split.
      intros. destruct H1. exists x1. assert (x [v ↦ x1 ]s == y0 [v ↦ x1 ]s). rewrite H. reflexivity. rewrite <- (IHy (x [v ↦ x1 ]s) (y0 [v ↦ x1 ]s) H2 x0 y1 H0).  auto.
      intros. destruct H1. exists x1. assert (x [v ↦ x1 ]s == y0 [v ↦ x1 ]s). rewrite H. reflexivity. rewrite (IHy (x [v ↦ x1 ]s) (y0 [v ↦ x1 ]s) H2 x0 y1 H0). auto.
    Qed.
    apply models_1.
  Defined.
  Notation "⟦ a ⟧" := (fun s h => models @ a @ s @ h) (at level 50, left associativity).
  Definition simply a a2 := forall s h, ⟦ a ⟧ s h -> ⟦ a2 ⟧ s h.
  Notation "a ⇒ a2" := (simply a a2) (at level 50).  
End AssertModel.  


