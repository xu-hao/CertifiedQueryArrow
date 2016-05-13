Require Import Assert Command Definitions Algebra.Monoid Expr Algebra.SetoidCat Algebra.Maybe Tactics Algebra.ListUtils Algebra.Functor Algebra.Applicative Algebra.Alternative Algebra.FoldableFunctor Algebra.PairUtils Algebra.Maybe Algebra.Monad Algebra.Lens.Lens Utils SetoidUtils SQL.
Require Import Coq.Structures.DecidableTypeEx List SetoidClass PeanoNat FMapWeakList Basics.



Lemma find_add_1 :forall A y y2 (val1 : A) x, y <> y2 -> FMapNat.find y2 (FMapNat.add y val1 x) = FMapNat.find y2 x.
Proof.
  intros. pose (FMapNat.find y2 x). assert ( FMapNat.find y2 x = o ). auto. destruct o.
  rewrite H0. apply FMapNat.find_1. apply FMapNat.add_2. auto. apply FMapNat.find_2. auto.
  rewrite H0. assert (~ (exists a, FMapNat.find (elt:=A) y2 (FMapNat.add y val1 x) = Some a)).
  intro. destruct H1. assert (FMapNat.find y2 x = Some x0). apply FMapNat.find_1. apply FMapNat.add_3 with (x:=y) (e:=x0) (e':=val1). auto. apply FMapNat.find_2. auto. destruct (FMapNat.find y2 x). inversion H0. inversion H2.
  destruct (FMapNat.find (elt:=A) y2 (FMapNat.add y val1 x)).
  destruct H1. exists a. auto.
  auto.
Defined.    
    
Lemma find_add_2 :forall A y y2 (val1 : A) x, y = y2 -> FMapNat.find y2 (FMapNat.add y val1 x) = Some val1.
Proof.
  intros. rewrite FMapNat.find_1 with (e:=val1).  reflexivity.
  apply FMapNat.add_1. auto.
Qed.

Lemma find_remove_2 :forall A y y2 x, y = y2 -> @FMapNat.find A y2 (FMapNat.remove y x) = None.
Proof.
Admitted.
  
Lemma find_remove_1 :forall A y y2 x, y <> y2 -> @FMapNat.find A y2 (FMapNat.remove y x) = FMapNat.find y2 x.
Proof.
Admitted.

Existing Instance FMapNatSetoid.
Instance In_Proper A (AS : Setoid A) : Proper (equiv ==> equiv ==> equiv) (@FMapNat.In A).
Proof.
Admitted.


Module SQLStore <: Store SQLValType.
  
  Definition t := store.
  Instance tS : Setoid t := storeS.

  Import SQLValType.

  Definition read : varS ~> storeS ~~> optionS valS.
    simple refine (injF2 (@FMapNat.find val) _).
    Lemma read_1 : Proper (equiv ==> equiv ==> equiv) (@FMapNat.find val).
    Proof.
      autounfold. intros. rewrite H, H0. reflexivity.
    Qed.
    apply read_1.
  Defined.

  Definition update : varS ~> valS ~~> storeS ~~> storeS.
    simple refine (injF3 (@FMapNat.add val) _).
    Lemma update_1 : Proper (equiv ==> equiv ==> equiv ==> equiv) (@FMapNat.add val).
    Proof.
      autounfold. intros. rewrite H. simpl in H0. rewrite H0. simpl in H1.
      simpl equiv. unfold FMapNat.Equal in *. intros.       destruct (Nat.eq_dec y y2).
      rewrite find_add_2. rewrite find_add_2. auto. auto. auto.
      rewrite find_add_1. rewrite find_add_1. auto. auto. auto.
    Qed.
    apply update_1.
  Defined.
  
  Definition delete : varS ~> storeS ~~> storeS.
    simple refine (injF2 (@FMapNat.remove val) _).
    Lemma delete_1 : Proper (equiv ==> equiv ==> equiv)
     (@FMapNat.remove val).
    Proof.
      autounfold. intros. rewrite H. simpl in *. unfold FMapNat.Equal. intros. destruct (Nat.eq_dec y y1).
      rewrite find_remove_2. rewrite find_remove_2. auto. auto. auto.
      rewrite find_remove_1. rewrite find_remove_1. auto. auto. auto.
    Qed.
    apply delete_1.
  Defined.

  Definition emptyStore : store := FMapNat.empty val.

  Lemma eq_store : forall s1 s2, (forall v, read @ v @ s1 == read @ v @ s2) -> s1 == s2.
  Proof.
    intros. simpl. unfold FMapNat.Equal. intros. simpl in H. pose (H y). assert (forall s1, FMapNat.find (elt:=val) y s1 = FMapNat.find (elt:=sqlVal) y s1).  auto. rewrite <- (H0 s1), <- (H0 s2).  clear H0. generalize y0. generalize (FMapNat.find (elt:=val) y s1), (FMapNat.find (elt:=val) y s2). intros. destruct o, o0. congruence. tauto. tauto. auto.
  Qed.
  
  Lemma read_update :
    forall s var val,
      read @ var @ (update @ var @ val @ s) == Some val.
  Proof.
    intros. simpl.
    rewrite FMapNat.find_1 with (e:= val0). auto.
    apply FMapNat.add_1.    auto.
  Qed.

  Lemma delete_update :
    forall s var val,
      delete @ var @ (update @ var @ val @ s) == delete @ var @ s.
  Proof.
    intros. simpl. unfold FMapNat.Equal. intros. destruct (Nat.eq_dec var y).
    rewrite find_remove_2. rewrite find_remove_2. auto. auto. auto.
    rewrite find_remove_1. rewrite find_remove_1. rewrite find_add_1. auto. auto. auto. auto.
  Qed.

  Lemma update_delete :
    forall s var1 val1,
       update @ var1 @ val1 @ (delete @ var1 @ s) == update @ var1 @ val1 @ s.
  Proof.
    intros. simpl. unfold FMapNat.Equal. intros. destruct (Nat.eq_dec var1 y).
    rewrite find_add_2. rewrite find_add_2. auto. auto. auto.
    rewrite find_add_1. rewrite find_add_1. rewrite find_remove_1. auto. auto. auto. auto.
  Qed.
  
  Lemma update_update :
    forall s var2 val1 val2,
      update @ var2 @  val2 @ (update @ var2 @ val1 @ s) == update @ var2 @ val2 @ s.
  Proof.
    intros. simpl. unfold FMapNat.Equal. intros. destruct (Nat.eq_dec var2 y).
    rewrite find_add_2. rewrite find_add_2. auto. auto. auto.
    rewrite find_add_1. rewrite find_add_1. rewrite find_add_1. auto. auto. auto. auto.
  Qed.
  
  Lemma read_update_diff_var :
    forall s var1 var2 val1,
      var1 <> var2 ->
      read @ var2 @ (update @ var1 @ val1 @ s) == read @ var2 @ s.
  Proof.
    intros. simpl. rewrite find_add_1. destruct  (FMapNat.find (elt:=val) var2 s). auto. auto. auto.
  Qed.
  
  Lemma update_update_diff_var :
    forall s var var2 val val2,
      var <> var2 ->
      update @ var2 @ val2 @ (update @ var @ val @ s) ==
      update @ var @ val @ (update @ var2 @ val2 @ s).
  Proof.
    intros. simpl. unfold FMapNat.Equal. intros. destruct (Nat.eq_dec var2 y).
    destruct (Nat.eq_dec var y). congruence.
    rewrite find_add_2. rewrite find_add_1. rewrite find_add_2. auto. auto. auto. auto.
    destruct (Nat.eq_dec var y).
    rewrite find_add_1. rewrite find_add_2. rewrite find_add_2. auto. auto. auto. auto.
    rewrite find_add_1. rewrite find_add_1. rewrite find_add_1. rewrite find_add_1. auto. auto. auto. auto. auto.
  Qed.

  Lemma delete_update_diff_var:
    forall s var var2 val,
      var <> var2 ->
      delete @ var2 @ (update @ var @ val @ s) == update @ var @ val @ (delete @ var2 @ s).
  Proof.
    intros. simpl. unfold FMapNat.Equal. intros. destruct (Nat.eq_dec var2 y).
    destruct (Nat.eq_dec var y). congruence.
    rewrite find_remove_2. rewrite find_add_1. rewrite find_remove_2. auto. auto. auto. auto.
    destruct (Nat.eq_dec var y).
    rewrite find_remove_1. rewrite find_add_2. rewrite find_add_2. auto. auto. auto. auto.
    rewrite find_remove_1. rewrite find_add_1. rewrite find_add_1. rewrite find_remove_1. auto. auto. auto. auto. auto.
  Qed.

  Lemma read_delete_diff_var :
    forall s var var2,
      var <> var2 ->
      read @ var2 @ (delete @ var @ s) == read @ var2 @ s.
  Proof.
    intros. simpl. rewrite find_remove_1. destruct (FMapNat.find (elt:=val) var2 s). auto. auto. auto.
  Qed.
  
    
  Lemma read_delete :
    forall s var,
      read @ var @ (delete @ var @ s) == None.
  Proof.
    intros. simpl. rewrite find_remove_2. auto. auto.
  Qed.

  Lemma read_empty:
    forall var,
      read @ var @ emptyStore == None.
  Proof.
    intros. simpl. auto.
  Qed.

End SQLStore.
