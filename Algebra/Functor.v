Require Import SetoidCat SetoidUtils.
Require Import SetoidClass.


Section Functor.

  Context
    {t : forall A, Setoid A -> Type}
    {tS : forall A (AS : Setoid A), Setoid (t A AS)}.


  Instance tSetoid {A} {AS : Setoid A} : Setoid (t A _) := tS _ AS.

  Class Functor :=
    {
      fmap : forall {A B} {AS : Setoid A} {BS : Setoid B}, (AS ~~> BS) ~> tS _ AS ~~> tS _ BS;
      functoriality_comp : forall {A B C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C}
                                  (f : AS ~> BS) (g : BS ~> CS),
                             fmap  @ (g ∘ f) == fmap  @ g ∘ fmap  @ f;
      
      functoriality_id: forall {A} {AS : Setoid A},
                         fmap  @ idS == idS
    }.

End Functor.

Section IdentityFunctor.

  Inductive IdentityFunc A {AS : Setoid A} := IdentityIso : A -> IdentityFunc A.

  Instance IdentityS {A} (AS : Setoid A) : Setoid (IdentityFunc A) :=
    {
      equiv a b := match a, b with
                     | IdentityIso _ a', IdentityIso _ b' => a'== b'
                   end
    }.
  Proof.
    split.
    autounfold. intros. destruct x. reflexivity.
    autounfold. intros. destruct x, y. symmetry. auto.
    autounfold. intros. destruct x, y, z. transitivity a0. auto. auto.
  Defined.
  
  Definition IdentityIso' A {AS : Setoid A} (a : IdentityFunc A) :=
    match a with
      | IdentityIso _ a' => a'
    end.
  
  

  Definition IdentityIsoS {A} (AS : Setoid A) : AS ~> IdentityS AS .
    simple refine (injF  (IdentityIso A) _).
    Lemma IdentityIsoS_1 : forall {A} {AS : Setoid A}, Proper (equiv ==> equiv) (IdentityIso A).
    Proof.
      autounfold. intros. simpl. auto.
    Qed.
    apply IdentityIsoS_1.
  Defined.

  Instance IdentityIso'_Proper {A} {AS : Setoid A}:  Proper (equiv ==> equiv) (IdentityIso' A).
  Proof.
    autounfold. unfold IdentityIso'. intros. destruct x, y.  auto. 
  Qed.

  Definition IdentityIsoS' {A} (AS : Setoid A) : IdentityS AS ~> AS .
    simple refine (injF  (IdentityIso' A) _).
  Defined.

  Definition idFunc_fmap {A B} {AS : Setoid A} {BS : Setoid B} :=
    flipS @ compS @ IdentityIsoS BS ∘ compS @ IdentityIsoS' AS.

  Instance IdentityFunctor : @Functor IdentityFunc (@IdentityS).
  Proof.

    exists (@idFunc_fmap).
    
    intros. simpl. arrequiv. 
    intros. simpl. arrequiv. destruct a. simpl. reflexivity.
  Defined.
End IdentityFunctor.

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
    autounfold. unfold IdentityIso'. intros. destruct x, y.  auto. 
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

Section ConstFunctor.
  Inductive ConstFunc B {BS : Setoid B} A {AS : Setoid A} := ConstIso : B -> ConstFunc B A.

  Instance ConstS {B} (BS : Setoid B) {A} (AS : Setoid A) : Setoid (ConstFunc B A) :=
    {
      equiv a b := match a, b with
                     | ConstIso _ _ a', ConstIso _ _ b' => a'== b'
                   end
    }.
  Proof.
    split.
    autounfold. intros. destruct x. reflexivity.
    autounfold. intros. destruct x, y. symmetry. auto.
    autounfold. intros. destruct x, y, z. transitivity b0. auto. auto.
  Defined.
  
  Definition ConstIso' B {BS : Setoid B} A {AS : Setoid A} (a : ConstFunc B A) :=
    match a with
      | ConstIso _ _ a' => a'
    end.
  
  Instance ConstIsoS_Proper  {B} {BS : Setoid B} {A} {AS : Setoid A} : Proper (equiv ==> equiv) (ConstIso B A).
  Proof.
    autounfold. intros. simpl. auto.
  Qed.

  Definition ConstIsoS {B} (BS : Setoid B) {A} (AS : Setoid A) : BS ~> ConstS BS AS :=
    injF  (ConstIso B A) _.

  Instance ConstIso'_Proper {B} {BS : Setoid B} {A} {AS : Setoid A}:  Proper (equiv ==> equiv) (ConstIso' B A).
  Proof.
    autounfold. unfold ConstIso'. intros. destruct x, y.  auto. 
  Qed.

  Definition ConstIsoS' {B} (BS : Setoid B) {A} (AS : Setoid A) : ConstS BS AS ~> BS := injF  (ConstIso' B A) _.

  Definition constFunc_fmap {C} {CS : Setoid C} {A B} {AS : Setoid A} {BS : Setoid B} :
    (AS ~~> BS) ~> (ConstS CS AS ~~> ConstS CS BS) :=
    constS (AS ~~> BS) @ (ConstIsoS CS BS ∘ ConstIsoS' CS AS).

  Instance ConstFunctor B (BS : Setoid B) : @Functor (ConstFunc B) (@ConstS B BS).
  Proof.

    exists (@constFunc_fmap B BS).
    
    intros. simpl. arrequiv. 
    intros. simpl. arrequiv. destruct a. simpl. reflexivity.
  Defined.

  Lemma ConstIso_iso : forall A B (AS : Setoid A) (BS : Setoid B) (a : B),
            match ConstIsoS BS AS @ a with
              | ConstIso _ _ a' => a'
            end = a.
  Proof.
    auto.
  Qed.

  Lemma ConstIsoS_iso : forall A B (AS : Setoid A) (BS : Setoid B) (a : B),
            ConstIsoS' _ _ @ (ConstIsoS BS AS @ a) = a.
  Proof.
    auto.
  Qed.

  Lemma ConstIso'_iso : forall A B (AS : Setoid A) (BS : Setoid B) a,
                          ConstIso B A (ConstIso' B A a) = a.
  Proof.
    intros. destruct a. auto. 
  Qed.

  Lemma ConstIsoS'_iso : forall A B (AS : Setoid A) (BS : Setoid B) a,
                          ConstIsoS BS AS @ (ConstIsoS' BS AS @ a) = a.
  Proof.
    intros. destruct a. auto. 
  Qed.

  Definition ConstCastS {A B C} (CS : Setoid C) (AS : Setoid A) (BS : Setoid B) : ConstS CS AS ~> ConstS CS BS := ConstIsoS _ _ ∘ ConstIsoS' _ _. 

End ConstFunctor.

Notation "a <$> b" := (fmap  @ a @ b) (at level 49, left associativity).

Section Utils.
  Context
    {t : forall A, Setoid A -> Type}
    {tS  : forall A (AS : Setoid A), Setoid (t A AS)}
    {func : @Functor t tS}.

  Lemma comp_eval : forall {A B C} {AS : Setoid A} {BS : Setoid B}{
                             CS : Setoid C}(a : A) (f : AS ~> BS) (g : BS~> CS), (comp f g) @ a == g @ (f @ a).
  Proof.
    intros. simpl. reflexivity.
  Qed.  

    Lemma fmap_fmap : forall {A B C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C}
                           (f : AS ~> BS) (g : BS ~> CS) (a : t A _),
                      g <$> (f <$> a) == (g ∘ f) <$> a.
  Proof.
    intros. rewrite <- comp_eval. rewrite functoriality_comp. reflexivity.
    Qed.
  Lemma fmap_idS_absorb : forall {A} {AS : Setoid A} (a : t A _), idS <$> a == a.
  Proof.
    intros. rewrite functoriality_id. simpl. reflexivity.
  Qed.

End Utils.
