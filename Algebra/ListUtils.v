Require Import Utils Algebra.SetoidCat Algebra.PairUtils Algebra.Monad Algebra.Monoid Algebra.Traversable Algebra.FoldableFunctor Algebra.Functor Algebra.SetoidUtils Algebra.Applicative Algebra.Alternative Tactics .

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import List.

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

Section AppS.
  Context
    {A : Type}
    {SA : Setoid A}.
  
  Definition appS : listS SA ~> listS SA ~~> listS SA.
    simple refine (injF2 (@app A) _).
  Defined.
  Context
    {m mS func}
    {app : @Applicative m mS func}.

  Lemma appS_consS : forall (a : m A _) (l n : m (list A) _),
                       appS <$> (consS <$> a <*> l) <*> n ==
                       consS <$> a <*> (appS <$> l <*> n).
  Proof.
    intros. simpl. rewrite <- (fmap_idS_absorb n) at 2. rewrite naturality_prod. repeat rewrite fmap_fmap. rewrite naturality_prod. rewrite <- (fmap_idS_absorb l) at 1. rewrite naturality_prod. rewrite fmap_fmap. rewrite <- (fmap_idS_absorb n) at 1. rewrite naturality_prod. rewrite <- associativity_applicative. repeat rewrite fmap_fmap. evalproper. evalproper. simpl. arrequiv. destruct a0. destruct p. reflexivity.
  Qed.

End AppS.

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
  Lemma fold_right_app :
    forall {A B} {SA : Setoid A} {SB : Setoid B} (f : A -> B -> B) (b : B) (l l2 : list A) ,
      fold_right f b (l ++ l2) = fold_right f (fold_right f b l2) l.
  Proof.
    intros. induction l.
    auto.
    simpl. congruence.
  Qed.

End Fold_rightS.

Section SequenceS.
  Context
    {m mS func}
    {mnd : @Applicative m mS func}
    {A : Type}
    {SA : Setoid A}.

  Fixpoint sequence  ( l : list (m A _)) : m (list A) _ :=
    match l with
      | [] => pure @ []
      | a :: s =>
        consS <$> a <*> sequence s
    end.

  Lemma sequence_cons :
    forall a l,
      sequence (a :: l) ==
      consS <$> a <*> sequence l.
  Proof.
    intros. simpl.  reflexivity.
  Qed.


  Global Instance sequence_Proper :  Proper (equiv ==> equiv) sequence.
  Proof.
    autounfold. intros.  generalize H. clear H. apply list_ind_2 with (T:=m A SA) (l1 := x)(l2:=y).
    reflexivity.
    intros. inversion H0.
    intros. inversion H0.
    intros. inversion H0. simpl. rewrite H4. rewrite H. reflexivity. auto. 
    
  Qed.

  Definition sequenceS  : listS (mS _ SA) ~> mS _ (listS SA).
    simple refine (injF sequence _).
  Defined.

  Lemma sequenceS_cons :
    forall (a : m A _) ( l : list (m A _)),
      sequenceS @ (  a ::  l) ==
      consS <$> a <*> sequenceS @ l.
  Proof.
    intros. simpl.    reflexivity.
  Qed.

  Lemma sequenceS_consS :
    forall (a : m A _) ( l : list (m A _)),
      sequenceS @ (consS @ a @ l) ==
      consS <$> a <*> sequenceS @ l.
  Proof.
    apply sequenceS_cons. 
  Qed.

  Lemma sequenceS_app: forall  ( l n : list (m A _)),
                         sequenceS @ (l ++ n) ==
                         appS <$> sequenceS @ l <*> sequenceS @ n.
  Proof.
    intros.
    induction l.
    simpl. rewrite <- (fmap_idS_absorb (sequence n)) at 2. repeat rewrite fmap_fmap. rewrite naturality_prod. rewrite <- (left_unit_applicative (sequence n)) at 1. repeat rewrite fmap_fmap. evalproper. evalproper. simpl. arrequiv. destruct a. reflexivity. 
    simpl (( _ :: _) ++ _).  repeat rewrite sequenceS_cons. rewrite IHl. rewrite appS_consS. reflexivity.
  Qed.
  Lemma sequence_nil :
    sequence [] == pure @ [].
  Proof.
    reflexivity.
  Qed.
  Lemma sequenceS_nil :
    sequenceS @ [] == pure @ [].
  Proof.
    reflexivity.
  Qed.
  
End SequenceS.

Section FMap.
  
  Existing Instance ComposeFunctor.
  Existing Instance Compose_Applicative.
  Existing Instance ComposeS.
  Context
    (t t' : forall A, Setoid A -> Type)
    (tS : forall A (AS : Setoid A), Setoid (t A AS))
    (tS' : forall A (AS : Setoid A), Setoid (t' A AS))
    func func'
    (app : @Applicative t tS func)
    (app' : @Applicative t' tS' func').
  
  Set Printing Implicit.
  Lemma ComposeIsoS'_prod :
    forall A B (AS : Setoid A) (BS : Setoid B) (a : t' (t A _) _) (b : t' (t B _) _),
      ComposeIsoS' _ @ ((ComposeIsoS _ @ a) ** (ComposeIsoS _ @ b)) ==
      produ <$> (a ** b).
  Proof.
    intros. simpl. reflexivity.
  Qed.
  Unset Printing Implicit.
End FMap. 

Section Generic.
  Context
    {m mS}
    {mnd : @Monad m mS}.



  Definition l A {AS : Setoid A} := list A.
  Instance lS {A} (AS : Setoid A) : Setoid (l A) := listS AS.

  Instance listFunctor : @Functor l (@lS).
  Proof.
    exists (@mapS).
    intros. simpl. arrequiv. induction a.
    reflexivity.
    simpl. constructor. reflexivity. auto.
    intros. simpl. arrequiv. induction a.
    reflexivity.
    simpl. constructor. reflexivity. auto.
  Defined.

  
  Definition list_fold A (AS : Setoid A) (A_monoid : @Monoid A AS) := @fold_rightS A A AS AS @ mappend @ mempty.
  
  Instance list_Foldable : @FoldableFunctor l (@lS) _.
  Proof.
    exists (list_fold).
    intros. simpl. destruct hom. induction a.
    simpl.  auto.
    simpl.  rewrite monoid_homomorphism_mappend. evalproper. auto.
  Defined.


  Existing Instance ComposeFunctor.
  Existing Instance Compose_Applicative.
  Existing Instance ComposeS.

  
  Existing Instance ComposeIso'_Proper.


  Definition listEmpty {A} {AS : Setoid A} : l A := nil.
  Instance list_Alternative : @Alternative l (@lS).
  Proof.
    exists (@listEmpty) (@appS).
    intros. reflexivity.
    intros. induction a.
    reflexivity.
    simpl. constructor. reflexivity. auto.
    intros. induction a.
    reflexivity.
    simpl. constructor. reflexivity. auto.
  Defined.

  Instance list_A_Monoid A AS : @Monoid (l A) (lS AS) := alternative_Monoid A AS.
  
  Definition pairS {A B} {AS : Setoid A} {BS : Setoid B} : AS ~>  BS ~~> AS ~*~ BS := curryS @ idS.

  Definition listProd0 {A B} {AS : Setoid A} {BS : Setoid B} : AS ~> listS BS ~~> listS (AS ~*~ BS) := mapS ∘ pairS .

  Definition listProd {A B} {AS : Setoid A} {BS : Setoid B} : listS AS ~> listS BS ~~> listS (AS ~*~ BS) := comp2S @ (flipS @ (mapS ∘ flipS @ listProd0)) @ fold.

  Lemma listProd_cons :
    forall {A B} {AS : Setoid A} {BS : Setoid B} (a : A) (l1 : l A) (l2 : l B),
      listProd @ (a :: l1) @ l2 == listProd0 @ a @ l2 ++ listProd @ l1 @ l2.  
  Proof.
    intros. simpl. reflexivity.
  Qed.
  Lemma listProd_app :
    forall {A B} {AS : Setoid A} {BS : Setoid B} (l0 l1 : l A) (l2 : l B),
      listProd @ (l0 ++ l1) @ l2 == listProd @ l0 @ l2 ++ listProd @ l1 @ l2.
  Proof.
    intros. induction l0.
    reflexivity.
    simpl (( _ :: _ ) ++ _) .  rewrite listProd_cons. rewrite listProd_cons. pose (associativity_monoid (listProd0 @ a @ l2) (listProd @ l0 @ l2) (listProd @ l1 @ l2)). simpl in *. rewrite e, IHl0. reflexivity. 
  Qed.
  Lemma listProd0_listProd :
    forall {A B C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C} (a : A) (l1 : l B) (l2 : l C),
      (listProd0 @ a @ (listProd @ l1 @ l2)) == associator <$> (listProd @ (listProd0 @ a @ l1) @ l2).  
  Proof.
    intros. induction l1.
    reflexivity.
    simpl. rewrite map_app. rewrite map_app. rewrite map_map. rewrite map_map. simpl (fun x : C =>
                                                                                        (fst (fst (id (id (a, a0), x))),
                                                                                         (snd (fst (id (id (a, a0), x))), snd (id (id (a, a0), x))))). unfold id. pose (app_Proper (map (fun x : C => (a, (a0, x))) l2) (map (fun x : C => (a, (a0, x))) l2)). apply r. reflexivity. auto.
  Qed.



  Instance list_Applicative : @Applicative l (@lS) _.
  Proof.
    exists ([tt]) (@listProd).
    intros. induction a.
    reflexivity.
    simpl. constructor. reflexivity. auto.
    intros. induction a.
    reflexivity.
    simpl. constructor. reflexivity. auto.
    intros. induction a.
    reflexivity.
    rewrite listProd_cons. rewrite listProd_cons. rewrite listProd_app. simpl fmap. rewrite mapS_app. rewrite IHa. apply app_Proper. induction b.  reflexivity.  rewrite (listProd0_listProd). reflexivity. reflexivity.
    intros. induction a.
    reflexivity.
    simpl. rewrite map_app. rewrite map_map. rewrite map_map. rewrite map_map. unfold id. pose (app_Proper (map (fun x : C => (f @ a, g @ x)) c) (map (fun x : C => (f @ a, g @ x)) c)). apply r. reflexivity.  simpl in IHa. repeat rewrite map_map in IHa. unfold id in IHa. auto.
  Defined.
  
  Instance list_Traversable : @Traversable l (@lS) _.
  Proof.
    exists (@sequenceS).
    intros. simpl. arrequiv. induction a.
    simpl. reflexivity.
    simpl. constructor. reflexivity. destruct (sequence a0). auto.

    intros. simpl_equiv. induction a.
    simpl. repeat rewrite fmap_fmap. evalproper. evalproper. simpl. arrequiv.
    rewrite sequenceS_cons. repeat rewrite comp_eval. rewrite mapS_cons. rewrite sequenceS_cons. rewrite IHa. unfold ap at 1. unfold fmap at 1 2. unfold ComposeFunctor. unfold compFunc_fmap. unfold comp2S. normalizecomp. evalproper.
    match goal with
      | |- _ <$> _ @ (_ @ ?a ** _ @ ?b) == _ =>
        rewrite (ComposeIsoS'_prod _ _ _ _ _ _ app' app'' _ _ _ _ a b)
    end.
    rewrite naturality_prod. rewrite <- uncurry_fmap_prod.  repeat rewrite fmap_fmap. evalproper. evalproper. simpl. arrequiv. simpl_let. reflexivity.

    intros. simpl_equiv. induction a.
    rewrite comp_eval. rewrite sequenceS_nil. rewrite app_trans_pure. reflexivity. auto.
    rewrite comp_eval. rewrite sequenceS_cons. rewrite app_trans_ap. rewrite app_trans_naturality.
    rewrite comp_eval. simpl (tr A AS <$> (a :: a0)). rewrite sequenceS_cons. evalproper. auto. auto.
  Defined.

End Generic.

Section MapM.


  Context
    {m mS}
    {func}
    {app : @Applicative m mS func}
    {A B : Type}
    {SA : Setoid A}
    {SB : Setoid B}.
  

  Existing Instance listFunctor.
  Existing Instance list_Applicative.
  Existing Instance list_Traversable.
  Definition mapM : (SA ~~> mS _ SB) ~> listS SA ~~> mS _ (listS SB) :=
    comp2S @ fmap @ sequenceA.


  Lemma mapM_cons :
    forall (f: SA ~> mS _ SB) (a : A) ( l : list A),
      mapM @ f @ ( a :: l) == consS <$> f @ a <*> mapM @ f @ l.
  Proof.
    intros.  unfold mapM at 1. unfold comp2S. normalizecomp. simpl fmap. rewrite mapS_cons. rewrite (sequenceS_cons).  evalproper.
  Qed.


  Lemma mapM_consS :
    forall (f: SA ~> mS _ SB) (a : A) ( l : list A),
      mapM @ f @ (consS @ a @ l) == consS <$> f @ a <*> mapM @ f @ l.
  Proof.
    apply mapM_cons.
  Qed.

  Lemma mapM_nil : forall  (f : SA ~> mS _ SB), mapM @ f @ nil == pure @ nil.
  Proof.
    intros. simpl. reflexivity.
  Qed.

  Lemma mapM_app :
    forall (f: SA ~> mS _ SB) (l l2 : list A),
      mapM @ f @ (  l ++ l2) ==
      appS <$> mapM @ f @ l <*> mapM @ f @ l2.
  Proof.
    intros. induction l0.
    simpl (([] ++ l2)). rewrite mapM_nil. rewrite fmap_pure. assert (appS @ [] == idS).
    simpl. arrequiv.
    rewrite H. rewrite ap_pure. rewrite fmap_idS_absorb. reflexivity.
    simpl (( _ :: _ ) ++ _ ). repeat rewrite mapM_cons. rewrite IHl0.
    simpl. normalizecomp. rewrite <- (fmap_idS_absorb (sequence (map (fun a0 : A => f @ a0) l2))) at 1. rewrite naturality_prod. rewrite fmap_fmap. rewrite naturality_prod. rewrite <- associativity_applicative. rewrite fmap_fmap. rewrite fmap_fmap.
    rewrite <- (fmap_idS_absorb (sequence (map (fun a0 : A => f @ a0) l0))) at 2. rewrite naturality_prod. repeat rewrite fmap_fmap. rewrite <- (fmap_idS_absorb (sequence (map (fun a0 : A => f @ a0) l2))) at 2. rewrite naturality_prod. repeat rewrite fmap_fmap. evalproper. evalproper. simpl. arrequiv. destruct a0. destruct p. simpl. reflexivity. 
  Qed.
  
  Lemma mapM_appS :
    forall (f: SA ~> mS _ SB) (l l2 :  (list A)),
      mapM @ f @ (appS @ l @ l2) ==
      appS <$> mapM @ f @ l <*> mapM @ f @ l2.
  Proof.
    apply mapM_app.
  Qed.
End MapM.


Section ConcatMap.
  Context
    {m mS}
    {func}
    {app : @Applicative m mS func}
    {A B : Type}
    {SA : Setoid A}
    {SB : Setoid B}.
  Definition concatMapM  : (SA ~~> mS _ (listS SB)) ~> listS SA ~~> mS _ (listS SB).
    simple refine (injF (fun f : SA ~> mS _ (listS SB) => injF (fun l => concatS <$> mapM @ f @ l) _ ) _).
    exact mS.
    exact func.
    exact func.
    exact app.
    Lemma concatMap_1 : forall f, Proper (equiv ==> equiv) (fun l : list A => concatS <$> mapM @ f @ l).
    Proof.
      repeat autounfold. intros. rewrite H. reflexivity.
    Qed.
    apply concatMap_1.

    Lemma concatMap_2 : forall pr, Proper (equiv ==> equiv)
                                          (fun f : SA ~> mS _ (listS SB) =>
                                             injF (fun l : list A => concatS <$> mapM @ f @ l) (pr f)).
    Proof.
      repeat autounfold. intros. arrequiv. evalproper. apply sequence_Proper. apply map_Proper. autounfold. intros. rewritesr.  reflexivity. 
    Qed.
    apply concatMap_2.
  Defined.
End ConcatMap.  

