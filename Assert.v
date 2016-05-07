Require Import Coq.Program.Basics.

Require Import Tactics Utils Algebra.SetoidUtils Algebra.SetoidCat Algebra.ListUtils Algebra.Monad Algebra.PairUtils Algebra.Maybe Expr Definitions.

Require Import FMapWeakList List RelationClasses Relation_Definitions Morphisms SetoidClass.

Module Type BuiltInPred.
  Parameter app : builtinS ~> listS valS ~~> optionS boolS.
End BuiltInPred.

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

Notation "a & b" := (aAnd a b) (left associativity, at level 81).
Notation "! a" := (aNot a) (at level 80).
Notation "[[ addr , p ]] ⟼ val" := (singleton addr p val) (at level 79).
Notation "a ∗ b" := (sepConj a b) (left associativity, at level 82).
Notation "a -∗ b" := (sepImp a b) (right associativity, at level 83).
Notation "'aexists' v , a" := (aExists v a) (at level 85).

Module Models (B: BuiltInExpr) (S : Store) (H : Heap).
  Module EM := ExprModel B S.
  Import EM S H.

  Reserved Notation "_⟦ a ⟧" (at level 20).

  Fixpoint _models (a : assertion) (s : S.t) (h : H.t) {struct a} : Prop :=
    match a with
      | emp => H.dom @ h == ∅
      | [[ expr , pred ]] ⟼ expr2 => exists val val2,
                   ⟦ expr ⟧expr s == Some val /\
                   ⟦ expr2 ⟧expr s == Some val2 /\
                   H.dom @ h == ﹛val﹜ /\
                   H.preds @ h == ﹛pred﹜ /\
                   h [val,pred] == Some val2
      | a0 ∗ a1 => exists h0 h1,
                     h0 ⊥ h1 /\ h0 ⋅ h1 == h /\ _⟦ a0 ⟧ s h0  /\ _⟦ a1 ⟧ s h1
      | a0 -∗ a1 => forall h',
                      h ⊥ h' -> _⟦ a0 ⟧ s h' -> _⟦ a1 ⟧ s (h ⋅ h') 
      | ! a => ~ _⟦ a ⟧ s h
      | a0 & a1 => _⟦ a0 ⟧ s h /\ _⟦ a1 ⟧ s h
      | atrue => True
      | aexists v, a => exists val, _⟦ a ⟧ (s [v ↦ val]s) h
    end
  where "_⟦ a ⟧" := (_models a).

  Definition models : assertionS ~> S.tS ~~> H.tS ~~> iff_setoid.
    simple refine (injF (fun a=> injF2 (fun s h => _models a s h) _) _).
Hint Unfold injF2. 
    Lemma models_1 : forall a, Proper (equiv ==> equiv ==> equiv) (fun (s : S.t) (h : t) => (_⟦ a ⟧) s h).
    Proof.
      repeat autounfold. induction a.
      intros. simpl.  rewrite H0.  tauto.
      intros. unfold _models. destruct exprEval.      simpl. split.
      intros. repeat destruct H1. destruct H2. destruct H3. destruct H4. exists x2. exists x3. split. assert (x1 x @ e == x1 y @ e). rewrite H. reflexivity. destruct (x1 x @ e), (x1 y @ e).  transitivity v. symmetry. auto. auto. auto. tauto. auto. split. assert (x1 x @ e0 == x1 y @ e0). rewrite H. reflexivity. destruct (x1 x @ e0), (x1 y @ e0). transitivity v. symmetry. auto. auto. auto. tauto. auto. split. rewrite <- H0. auto. split. rewrite <- H0. auto. assert (x0 [x2, p] == y0 [x2, p]). rewrite H0. reflexivity. destruct (x0 [x2, p]), (y0 [x2, p]). transitivity v. symmetry. auto. auto. auto. tauto. auto.
      intros. repeat destruct H1. destruct H2. destruct H3. destruct H4. exists x2. exists x3. split. assert (x1 x @ e == x1 y @ e). rewrite H. reflexivity. destruct (x1 x @ e), (x1 y @ e).  transitivity v0. auto. auto. tauto. auto. auto. split. assert (x1 x @ e0 == x1 y @ e0). rewrite H. reflexivity. destruct (x1 x @ e0), (x1 y @ e0). transitivity v0. auto. auto. tauto. auto. auto. split. rewrite  H0. auto. split. rewrite  H0. auto. assert (x0 [x2, p] == y0 [x2, p]). rewrite H0. reflexivity. destruct (x0 [x2, p]), (y0 [x2, p]). transitivity v0.  auto. auto. tauto. auto. auto.
      intros. simpl. split.
      intros. repeat destruct H1. exists x1. exists x2. rewrite <- (IHa1 _ _ H x1 x1) , <- (IHa2 _ _ H x2 x2). rewrite <- H0. auto. reflexivity. reflexivity. 
      intros. repeat destruct H1. exists x1. exists x2. rewrite (IHa1 _ _ H x1 x1) , (IHa2 _ _ H x2 x2). rewrite H0. auto. reflexivity. reflexivity. 

      intros. simpl. split.
      intros. rewrite <- (IHa2 _ _ H (x0 ⋅ h') (y0 ⋅ h')). apply H1. rewrite H0. auto. rewrite (IHa1 _ _ H h' h'). auto. reflexivity. rewrite H0. reflexivity.
      intros. rewrite (IHa2 _ _ H (x0 ⋅ h') (y0 ⋅ h')). apply H1. rewrite <- H0. auto. rewrite <- (IHa1 _ _ H h' h'). auto. reflexivity. rewrite H0. reflexivity.

      intros. simpl. tauto.
      intros. simpl. rewrite (IHa1 _ _ H _ _ H0), (IHa2 _ _ H _ _ H0). tauto.
      intros. simpl. rewrite (IHa _ _ H _ _ H0). tauto.
      intros. simpl. split.
      intros. destruct H1. exists x1. assert (x [v ↦ x1 ]s == y [v ↦ x1 ]s). rewrite H. reflexivity. rewrite <- (IHa (x [v ↦ x1 ]s) (y [v ↦ x1 ]s) H2 x0 y0 H0).  auto.
      intros. destruct H1. exists x1. assert (x [v ↦ x1 ]s == y [v ↦ x1 ]s). rewrite H. reflexivity. rewrite(IHa (x [v ↦ x1 ]s) (y [v ↦ x1 ]s) H2 x0 y0 H0). auto.
    Qed.
    apply models_1.
    Lemma models_2 : forall pr, Proper (equiv ==> equiv)
     (fun a : assertion =>
        injF2 (fun (s : S.t) (h : t) => (_⟦ a ⟧) s h) (pr a)).
    Proof.
      repeat autounfold. intros. arrequiv.
    Qed.
    apply models_2.
  Defined.
  Notation "⟦ a ⟧" := (fun s h => models @ a @ s @ h) (at level 50, left associativity).
  Definition simply a a2 := forall s h, ⟦ a ⟧ s h -> ⟦ a2 ⟧ s h.
  Notation "a ⇒ a2" := (simply a a2) (at level 50).  
End Models.  


