Require Import SetoidClass SetoidCat Algebra.SetoidCat.MaybeUtils Tactics Monoid Pointed.

Section Maybe_First_Monoid.
  Definition _maybe_first_mappend {C} {CS : Setoid C}  (a b : maybe C) : maybe C :=
    match a with
      | None => b
      | Some a' => a
    end
  .

  Instance _maybe_first_mappend_Proper {C} {CS : Setoid C}  : Proper (equiv ==> equiv ==> equiv) _maybe_first_mappend.
  Proof.
    autounfold. intros. unfold _maybe_first_mappend. matchequiv. auto. auto. 
  Qed.

  Definition maybe_first_mappend {C} {CS : Setoid C} : maybeS CS ~> maybeS CS ~~> maybeS CS := injF2 _maybe_first_mappend _.
  
  Instance maybe_mappend_PointedFunction2 A AS : PointedFunction2 (@maybe_first_mappend A AS).
  Proof.
    split. simpl. auto.
  Qed.

  Instance maybe_first_Monoid {C} {CS : Setoid C} : @Monoid (maybe C) _.
  Proof.
    exists (None) (maybe_first_mappend).
    intros. simpl. destruct a. reflexivity. reflexivity.
    intros. destruct a. simpl. reflexivity. simpl. auto.
    intros. destruct a. simpl. reflexivity. destruct b. simpl. reflexivity. simpl. destruct c.  reflexivity. reflexivity.
  Defined.

End Maybe_First_Monoid.

Section Maybe_A_Monoid.
  Definition _maybe_mappend {C} {CS : Setoid C} {mon : @Monoid C CS} (a b : maybe C) : maybe C :=
    match a with
      | None => b
      | Some a' => match b with
                     | None => a
                     | Some b' => Some (mappend @ a' @ b')
                   end
    end
  .

  Instance _maybe_mappend_Proper {C} {CS : Setoid C} {mon : @Monoid C CS} : Proper (equiv ==> equiv ==> equiv) _maybe_mappend.
  Proof.
    autounfold. intros. unfold _maybe_mappend. matchequiv. matchequiv. simpl in *. rewritesr.  auto. auto.
  Qed.

  Definition maybe_mappend {C} {CS : Setoid C} {mon : @Monoid C CS}: maybeS CS ~> maybeS CS ~~> maybeS CS := injF2 _maybe_mappend _.
  
  Instance maybe_A_Monoid {C} {CS : Setoid C} {mon : @Monoid C CS}: @Monoid (maybe C) _.
  Proof.
    exists (None) (maybe_mappend).
    intros. simpl. reflexivity. 
    intros. simpl. destruct a. simpl. reflexivity. simpl. auto.
    intros. simpl. destruct a. simpl. destruct b. simpl. destruct c. rewrite associativity_monoid. reflexivity. reflexivity. destruct c. simpl. reflexivity. simpl. reflexivity. destruct b. simpl. destruct c. reflexivity. reflexivity. destruct c. simpl. reflexivity. simpl. auto.
  Defined.
End Maybe_A_Monoid.
