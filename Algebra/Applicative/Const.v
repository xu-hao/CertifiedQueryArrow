Require Import SetoidCat SetoidUtils PairUtils UnitUtils Algebra.Applicative Algebra.Functor.Const Algebra.Monoid.

Require Import SetoidClass.

Section ConstApplicative.
  Context
    {C}
    {CS : Setoid C}
    {mon : @Monoid C CS}.

  Definition constFunc_unitA := ConstIsoS CS unitS @ mempty.
  Definition constFunc_prod {A B} {AS : Setoid A} {BS : Setoid B} : ConstS CS AS ~> ConstS CS BS ~~> ConstS CS (AS ~*~ BS) :=
    flipS @ compS @ ConstIsoS CS (AS ~*~ BS)
          ∘ compS @ ConstIsoS' CS BS
          ∘ mappend ∘ ConstIsoS' CS AS.

  Existing Instance ConstFunctor.
  Existing Instance ConstS.

  Instance Const_Applicative : @Applicative (ConstFunc C) _ _.
  
  Proof.

    exists (@constFunc_unitA) (@constFunc_prod).
    
    intros. simpl. destruct a. rewrite left_unit_monoid. reflexivity.
    intros. simpl. destruct a. rewrite right_unit_monoid. reflexivity. 
    intros. simpl. rewrite associativity_monoid. reflexivity. 
    intros. simpl. reflexivity. 
  Defined.
End ConstApplicative.

