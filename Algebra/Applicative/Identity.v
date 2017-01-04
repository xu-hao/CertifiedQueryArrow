Require Import SetoidCat SetoidUtils Algebra.Functor Algebra.Monoid PairUtils Algebra.Utils UnitUtils Algebra.Applicative Algebra.Functor.Identity.

Require Import SetoidClass.

Section IdentityApplicative.


  Definition idFunc_unitA := IdentityIso unit tt.
  Definition idFunc_prod {A B} {AS : Setoid A} {BS : Setoid B} : IdentityS AS ~> IdentityS BS ~~> IdentityS (AS ~*~ BS) :=
    flipS @ compS @ IdentityIsoS (AS ~*~ BS)
          ∘ compS @ IdentityIsoS' BS
          ∘ curryS @ @idS _ (AS ~*~ BS) ∘ IdentityIsoS' AS.

  Existing Instance IdentityFunctor.
  Existing Instance IdentityS.

  Instance Identity_Applicative : @Applicative IdentityFunc _ _.
  
  Proof.

    exists (@idFunc_unitA) (@idFunc_prod).
    
    intros. simpl. destruct a. reflexivity.
    intros. simpl. destruct a. reflexivity. 
    intros. simpl. split. reflexivity. split. reflexivity. reflexivity.
    intros. simpl. split. reflexivity. reflexivity.
  Defined.
End IdentityApplicative.

