Require Import SetoidCat SetoidUtils Algebra.Functor.
Require Import SetoidClass.

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

