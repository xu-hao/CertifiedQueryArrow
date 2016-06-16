Require Import SetoidClass SetoidCat Monoid Algebra.SetoidCat.PropUtils.

Section Aux.

    Instance and_Monoid : @Monoid Prop iff_setoid.
    Proof.
      exists True andS.
      intros. simpl. tauto.
      intros. simpl. tauto.
      intros. simpl. tauto.
    Defined.
    Instance or_Monoid : @Monoid Prop iff_setoid.
    Proof.
      exists False orS.
      intros. simpl. tauto.
      intros. simpl. tauto.
      intros. simpl. tauto.
    Defined.
End Aux.