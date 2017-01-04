Require Import Algebra.Utils Algebra.SetoidCat Algebra.SetoidCat.PairUtils Algebra.Monad Algebra.Monoid Algebra.SetoidCat.SetoidUtils Algebra.Tactics Algebra.SetoidCat.BoolUtils.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Lists.List.

Import ListNotations.


Program Instance listS {A} (SA : Setoid A) : Setoid (list A).

Instance map_Proper {A B : Type} {SA : Setoid A} {SB : Setoid B} : Proper ((equiv ==> equiv) ==> equiv ==> equiv) (@map A B).
Proof.
  unfold Proper, respectful in *. intros x y H lx ly. generalize x y H.
  apply list_ind_2 with (l1 := lx) (l2 := ly).
  intros.  simpl. constructor.
  intros. inversion H2.
  intros. inversion H2.
  intros. simpl in *. inversion H2. constructor. auto. auto. 
Qed.

Instance cons_Proper {A} {SA : Setoid A} : Proper (equiv ==> equiv ==> equiv) (@cons A).
Proof.
  unfold Proper, respectful in *. intros x y H lx ly. generalize x y H.
  apply list_ind_2 with (l1 := lx) (l2 := ly).
  intros. constructor. auto. auto.
  intros. inversion H2.
  intros. inversion H2.
  intros. simpl. constructor. auto. auto.
Qed.

Instance app_Proper {A} {SA : Setoid A}  : Proper ( equiv ==> equiv ==> equiv) (@app A).
Proof.
  unfold Proper in *. unfold respectful in *. intros x y.
  apply list_ind_2 with (l1:=x)(l2:=y).
  auto.
  intros. inversion H0.
  intros. inversion H0.
  intros. simpl in *. inversion H0. constructor. auto. auto. 
Qed.


Instance concat_Proper {A} {SA : Setoid A}  : Proper ( equiv ==> equiv) (@concat A).
Proof.
  unfold Proper in *. unfold respectful in *. intros x y.
  apply list_ind_2 with (l1:=x) (l2:=y).
  intros. reflexivity. 
  intros. inversion H0.
  intros. inversion H0.
  intros. simpl in *. inversion H0. apply app_Proper. auto. apply H. auto.
Qed.

Instance fold_right_Proper {A B : Type} {SA : Setoid A} {SB : Setoid B} : Proper ((equiv ==> equiv ==> equiv) ==> equiv ==> equiv ==> equiv) (@fold_right B A).
Proof.
  unfold Proper, respectful in *. intros f g H x y H2 lx ly.
  apply list_ind_2 with (l1 := lx) (l2 := ly).
  auto.
  intros. inversion H1.
  intros. inversion H1.
  intros. simpl in *. inversion H1. apply H. auto. auto.
Qed.

Instance fold_left_Proper {A B : Type} {SA : Setoid A} {SB : Setoid B} : Proper ((equiv ==> equiv ==> equiv) ==> equiv ==> equiv ==> equiv) (@fold_left B A).
Proof.
  unfold Proper, respectful in *. intros f g H lx ly.
  apply list_ind_2 with (l1 := lx) (l2 := ly). 
  auto.
  intros. inversion H1.
  intros. inversion H1.
  intros. simpl in *. inversion H1. apply H0. auto. apply H. auto. auto.
Qed.


Instance null_Proper {A} {SA : Setoid A}  : Proper (equiv ==> equiv) (@null A).
Proof.
  unfold Proper, respectful in *. intros. unfold null. generalize H. clear H. apply list_ind_2 with (l1:=x)(l2:=y).
  intros. reflexivity.
  intros. inversion H0.
  intros. inversion H0.
  intros. reflexivity.
Qed.


Section ConcatS.
  Context
    {A : Type}
    {SA : Setoid A}.

  Definition concatS : listS (listS SA) ~> listS SA.
    refine (injF (@concat A) _).
  Defined.
End ConcatS.

Section ConsS.
  Context
    {A : Type}
    {SA : Setoid A}.

  Definition consS : SA ~> listS SA ~~> listS SA.
    simple refine (injF2 (@cons A) _).
  Defined.
End ConsS.


Section MapS.

  Context
    {A B : Type}
    {SA : Setoid A}
    {SB : Setoid B}.

  Definition mapS : (SA ~~> SB) ~> listS SA ~~> listS SB.
    simple refine (injF (fun f => injF (map (fun a => f @ a)) _) _).
    Lemma mapProper0_1 :forall f, Proper (equiv ==> equiv) (map (fun a : A => f @ a)).
    Proof.
      unfold Proper, respectful. intros. generalize H. clear H. apply list_ind_2 with (l1:=x) (l2:=y).
      intros. simpl. auto.
      intros. inversion H0.
      intros. inversion H0.
      intros. inversion H0. simpl. constructor.
      rewrite H4. reflexivity.
      apply H. auto.
    Qed.
    apply mapProper0_1.
    Lemma mapProper0_2 : forall pr, Proper (equiv ==> equiv)
                                           (fun f : SA ~> SB => injF (map (fun a : A => f @ a)) (pr f)).
    Proof.
      unfold Proper, respectful. intros. arrequiv. induction a.
      simpl. auto.
      simpl. constructor. 
      apply H.
      apply IHa.
    Qed.
    apply mapProper0_2.
  Defined.
  
  Lemma mapS_cons : forall  (f : SA ~> SB) (a : A) (n : list A), mapS @ f @ (a :: n) == (f @ a) :: (mapS @ f @ n).
  Proof.
    intros. reflexivity.
  Qed.


  Lemma mapS_app :
    forall (l0 l1 : list A) (f : SA ~> SB),
      mapS @ f @ (l0 ++ l1) == mapS @ f @ l0 ++ mapS @ f @ l1.
  Proof.
    intros. induction l0.
    reflexivity.
    simpl.  constructor. reflexivity. auto.
  Qed.
  Lemma map_nil: forall A B (BS : Setoid B) (f : A -> B),
                   map f [] == [].
  Proof.
    reflexivity.
  Qed.

   

End MapS.
 Lemma mapS_mapS : forall A (AS : Setoid A) B (BS : Setoid B) C (CS : Setoid C) (f : AS ~> BS) (g : BS ~> CS) (l : list A),
                        mapS @ g @ (mapS @ f @ l) = mapS @ (comp f g) @ l.
    Proof.
      intros. unfold mapS. normalize. rewrite map_map. reflexivity.
    Qed.

Section Fold_rightS.
  Context
    {A B} {SA : Setoid A} {SB : Setoid B}.

  Definition fold_rightS : (SA ~~> SB ~~> SB) ~> SB ~~> listS SA ~~> SB.
    simple refine (injF3 (fun (f : SA ~> SB ~~> SB) (b : B) (l : list A) => fold_right (fun a b => f @ a @ b) b l) _).
    Lemma fold_rightProper_1 : Proper (equiv ==> equiv ==> equiv ==> equiv)
                                      (fun (f : SA ~> SB ~~> SB) (b : B) (l : list A) =>
                                         fold_right (fun (a : A) (b0 : B) => f @ a @ b0) b l).

    
    Proof.
      autounfold. intros. generalize H1. clear H1. apply list_ind_2 with (l1:=x1) (l2:=y1).
      intros. auto.
      intros. inversion H2.
      intros. inversion H2.
      intros. inversion H2. simpl. rewrite H1. rewritesr. auto.
    Qed.
    apply fold_rightProper_1.
  Defined.

  Lemma fold_rightS_cons : forall (f : SA ~> SB ~~> SB) (b : B) (a : A) (l : list A),
                             fold_rightS @ f @ b @ (a :: l) == f @ a @ (fold_rightS @ f @ b @ l).
  Proof.
    intros. simpl. reflexivity.
  Qed.
  Lemma fold_rightS_app : forall (f : SA ~> SB ~~> SB) (b : B) (l n : list A),
                            fold_rightS @ f @ b @ (l ++ n) == fold_rightS @ f @ (fold_rightS @ f @ b @ n) @ l.
  Proof.
    intros. induction l.
    reflexivity.
    simpl ((_ :: _) ++ _).  repeat  rewrite fold_rightS_cons. rewritesr. 
  Qed.
  Lemma fold_right_cons : forall A B (f : A -> B -> B) (b : B) (a : A) (l : list A),
                            fold_right f b (a :: l) = f a (fold_right f b l).
  Proof.
    reflexivity.
  Qed.
  

  Lemma fold_right_app :
    forall {A B} {SA : Setoid A} {SB : Setoid B} (f : A -> B -> B) (b : B) (l l2 : list A) ,
      fold_right f b (l ++ l2) = fold_right f (fold_right f b l2) l.
  Proof.
    intros. induction l.
    auto.
    simpl. congruence.
  Qed.

End Fold_rightS.

Section AppS.
  Context
    {A : Type}
    {SA : Setoid A}.
  
  Definition appS : listS SA ~> listS SA ~~> listS SA.
    simple refine (injF2 (@app A) _).
  Defined.
End AppS.
