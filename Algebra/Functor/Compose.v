Require Import SetoidCat SetoidUtils Algebra.Functor.
Require Import SetoidClass.


Section ComposeFunctor.

  Context
    {t t' : forall A, Setoid A -> Type}
    {tS  : forall A (AS : Setoid A), Setoid (t A AS)}
    {tS'  : forall A (AS : Setoid A), Setoid (t' A AS)}
    {func : @Functor t tS} {func' : @Functor t' tS'}.

  Inductive ComposeFunc A {AS : Setoid A} := ComposeIso : t' (t A _) _ -> ComposeFunc A.

  Instance ComposeS {A} (AS : Setoid A) : Setoid (ComposeFunc A) :=
    {
      equiv a b := match a, b with
                     | ComposeIso _ a', ComposeIso _ b' => a'== b'
                   end
    }.
  Proof.
    split.
    autounfold. intros. destruct x. reflexivity.
    autounfold. intros. destruct x, y. symmetry. auto.
    autounfold. intros. destruct x, y, z. transitivity t1. auto. auto.
  Defined.
  
  Definition ComposeIso' A {AS : Setoid A} (a : ComposeFunc A) :=
    match a with
      | ComposeIso _ a' => a'
    end.

  Definition ComposeIsoS {A} (AS : Setoid A) : tS' _ (tS _ AS) ~> ComposeS AS .
    simple refine (injF  (ComposeIso A) _).
    Lemma ComposeIsoS_1 : forall {A} {AS : Setoid A}, Proper (equiv ==> equiv) (ComposeIso A).
    Proof.
      autounfold. intros. simpl. auto.
    Qed.
    apply ComposeIsoS_1.
  Defined.

  Instance ComposeIso'_Proper {A} {AS : Setoid A} : Proper (equiv ==> equiv) (ComposeIso' A).
  Proof.
    autounfold. unfold ComposeIso'. intros. destruct x, y.  auto. 
  Qed.

  Definition ComposeIsoS' {A} (AS : Setoid A) : ComposeS AS ~> tS' _ (tS _ AS) .
    simple refine (injF  (ComposeIso' A) _).
  Defined.

  Definition compFunc_fmap {A B} {AS : Setoid A} {BS : Setoid B} :
    (AS ~~> BS) ~> (ComposeS AS ~~> ComposeS BS).
    simple refine (injF (fun f=> ComposeIsoS BS ∘
                                             @fmap t' _ _ _ _ _ _ @ (@fmap t _ _ _ _ _ _ @ f) ∘ ComposeIsoS' AS) _).
    exact func'.
    exact func.
    Lemma compFunc_fmap_1 : forall {A B} {AS : Setoid A} {BS : Setoid B}, Proper (equiv ==> equiv) (fun f : AS ~> BS => ComposeIsoS BS ∘ @fmap t' _ _ _ _ _ _ @ (@fmap t _ _ _ _ _ _ @ f) ∘ ComposeIsoS' AS).
    Proof.
      autounfold. intros. rewrite H. reflexivity.
    Qed.
    apply compFunc_fmap_1.
  Defined.
  
  Instance ComposeFunctor : @Functor ComposeFunc (@ComposeS).
  Proof.
    exists (@compFunc_fmap).
    intros. simpl. arrequiv. rewrite functoriality_comp. apply functoriality_comp. 
    intros. simpl. arrequiv. destruct a. simpl. rewrite functoriality_id. apply functoriality_id.
  Defined.

End ComposeFunctor.

