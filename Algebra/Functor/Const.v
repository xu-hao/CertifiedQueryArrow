Require Import SetoidCat SetoidUtils Algebra.Functor.
Require Import SetoidClass.

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
