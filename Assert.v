Require Import Coq.Program.Basics.

Require Import Tactics Utils Algebra.SetoidUtils Algebra.SetoidCat Algebra.SetoidCat.ListUtils Algebra.Monad Algebra.SetoidCat.PairUtils Algebra.SetoidCat.MaybeUtils Algebra.Monad.Maybe Expr Definitions.

Require Import FMapWeakList List RelationClasses Relation_Definitions Morphisms SetoidClass.


Section Assert.
  Context
    {pred : Type}
    {builtin : Type}.

  Definition expr := @expr builtin.

  Inductive assertion :=
  | emp : assertion
  | singleton : expr -> pred -> expr -> assertion
  | sepConj : assertion -> assertion -> assertion
  | sepImp : assertion -> assertion -> assertion
  | atrue : assertion
  | aAnd : assertion -> assertion -> assertion
  | aNot : assertion -> assertion
  | aExists : var -> assertion -> assertion
  .

  Program Instance assertionS : Setoid assertion.


End Assert.

  Notation "a & b" := (aAnd a b) (left associativity, at level 81).
  Notation "! a" := (aNot a) (at level 80).
  Notation "[[ addr , p ]] ⟼ val" := (singleton addr p val) (at level 79).
  Notation "a ∗ b" := (sepConj a b) (left associativity, at level 82).
  Notation "a -∗ b" := (sepImp a b) (right associativity, at level 83).
  Notation "'aexists' v , a" := (aExists v a) (at level 85).
  
  Module AssertModel (TT: TypeType ) (AT : AddrType ) (PT : PredType) (VT : ValType)  (S : Store VT) (H : Heap TT AT PT VT) (B: BuiltInExpr VT S).
  Module EM := ExprModel VT S B.
  Module HU := HeapUtils TT AT PT VT H.
  Import TT AT PT VT EM S H B HU.
  Definition assertion := @assertion pred builtInExpr.
  Instance assertionS : Setoid assertion := @assertionS pred builtInExpr.

  Fixpoint _models (a : assertion) (s : S.t) (h : H.t) {struct a} : Prop :=
    match a with
      | emp => ~exists a, inDom @ a @ h
      | [[ expr , pred ]] ⟼ expr2 =>
        exists val val2 addr1,
        ⟦ expr ⟧expr s == Some val /\
        extractAddr @ val == Some addr1 /\                             
        ⟦ expr2 ⟧expr s == Some val2 /\
        singleton @ addr1 @ pred @ val2 @ h
      | a0 ∗ a1 => exists h0 h1,
                     h0 ⊥ h1 /\ h0 ⋅ h1 == h /\ _models a0 s h0  /\ _models a1 s h1
      | a0 -∗ a1 => forall h',
                      h ⊥ h' -> _models a0 s h' -> _models a1 s (h ⋅ h') 
      | ! a => ~ _models a s h
      | a0 & a1 => _models a0 s h /\ _models a1 s h
      | atrue => True
      | aexists v, a => exists val, _models a (S.update @ v @ val @ s) h
    end.

  Definition models : assertionS ~> S.tS ~~> H.tS ~~> iff_setoid.
    simple refine (injF3 _models _).
    Lemma models_1 : Proper (equiv ==> equiv ==> equiv ==> equiv) _models.
    Proof.
      autounfold. intros x y H. rewrite H. clear x H. induction y.
      intros. simpl.  split.
      intros. intro. apply H1. destruct H2. destruct H2.  destruct H2. exists x1. exists x2. exists x3. equiv (x0 [x1, x2]) ( y0 [x1, x2]). simpl in H3. unfold maybe_equiv in *. transitivity v0. auto. auto. auto.
      intros. intro. apply H1. destruct H2. destruct H2.  destruct H2. exists x1. exists x2. exists x3. equiv (x0 [x1, x2]) ( y0 [x1, x2]). simpl in H3. unfold maybe_equiv in *. transitivity v. symmetry. auto. auto. auto.
      intros. unfold _models. split.
      intro. destruct H1 as [x1 [x2 [x3 ? ] ] ]. exists x1. exists x2. exists x3. rewrite <- H. rewrite <- H0. tauto. 
      intro. destruct H1 as [x1 [x2 [x3 ? ] ] ]. exists x1. exists x2. exists x3. rewrite H. rewrite H0. tauto. 
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


