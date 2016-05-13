Require Import Algebra.Functor Algebra.Applicative Algebra.SetoidCat Algebra.ListUtils Algebra.PairUtils Algebra.Maybe Algebra.SetoidUtils Algebra.Monad Algebra.Maybe Tactics Utils VectorUtils Algebra.Lens.LensTypes Algebra.Pointed.
Require Import SetoidClass List Coq.Classes.RelationClasses Coq.Arith.PeanoNat Coq.Arith.Compare_dec.
Import ListNotations.


Instance length_Proper A (AS : Setoid A) : Proper (equiv ==> equiv) (@length A).
  Proof.
    autounfold. intros. generalize H. clear H. apply list_ind_2 with (l1:=x) (l2:=y).
    reflexivity.
    intros. inversion H0.
    intros. inversion H0.
    intros. simpl. rewrite H. auto. inversion H0. auto.
  Qed.

  Instance nth_error_Proper A (AS : Setoid A) : Proper (equiv ==> equiv ==> equiv) (@nth_error A).
  Proof.
    autounfold. intros. generalize H x0 y0 H0. clear H x0 y0 H0. apply list_ind_2 with (l1:=x) (l2:=y).
    intros. rewritesr. 
    intros. inversion H0.
    intros. inversion H0.
    intros. inversion H0. simpl. simpl in H1.  rewrite H1. destruct y0. simpl. auto.
    simpl. apply H. auto. reflexivity.
  Qed.

Fixpoint listS_update {f fS func} {app : @Applicative f fS func} {A} {AS : Setoid A} (n:nat) (l:list A)  (t:AS ~>  fS _ AS) {struct n} :  f (list A) _ :=
  match n, l with
    | 0,   old_v::rest => consS <$> t @ old_v <*> pure @ rest
    | S n, v'::rest    => consS <$> pure @ v' <*> listS_update n rest  t 
    | _,   nil         => pure @ nil
  end.


Instance listS_update_Proper {f fS func} {app : @Applicative f fS func} A (AS : Setoid A): Proper (equiv ==> equiv ==> equiv ==> equiv) (listS_update).
Proof.
  autounfold. intros. rewrite H.  clear x H. generalize y H0. clear H0. apply list_ind_2 with (l1:=x0) (l2:=y0).
  intros. induction y2.
  simpl. evalproper. 
  simpl. evalproper. 
  intros. inversion H0.
  intros. inversion H0.
  intros. inversion H0. induction y2.
  simpl. evalproper. evalproper. rewritesr. evalproper. evalproper. arrequiv. auto.
  simpl. evalproper. evalproper. evalproper. evalproper. evalproper. evalproper. arrequiv. auto. 
Qed.

Definition list_updateS {f fS func} {app : @Applicative f fS func} {A} {AS : Setoid A} := injF3 (@listS_update f fS func app A AS) _.

Fixpoint list_update' {A} {AS : Setoid A} (n:nat) (l:list A)  (a:A ) {struct n} :  list A :=
  match n, l with
    | 0,   old_v::rest => a :: rest
    | S n, v'::rest    => v' :: list_update' n rest  a 
    | _,   nil         => nil
  end.


Instance list_update'_Proper A (AS : Setoid A): Proper (equiv ==> equiv ==> equiv ==> equiv) (list_update').
Proof.
  autounfold. intros. rewrite H.  clear x H. generalize y H0. clear H0. apply list_ind_2 with (l1:=x0) (l2:=y0).
  intros. induction y2.
  simpl.  reflexivity. 
  simpl. reflexivity. 
  intros. inversion H0.
  intros. inversion H0.
  intros. inversion H0. induction y2.
  simpl.  constructor.  auto. auto. 
  simpl. constructor. auto. apply H. auto. 
Qed.

Definition list_updateS' {A} {AS : Setoid A} := injF3 (@list_update' A AS) _.

Definition _nthTraversal' {A} {AS : Setoid A} (n : nat) : _Traversal' (list A) A.
  unfold _Traversal'. intros. refine (match nth_error X0 n with
                                    | None => pure @ X0
                                    | Some a => listS_update n X0  X
                                  end).
Defined.

Definition _nthTraversal {f fS func} {app : @Applicative f fS func} {A} {AS : Setoid A} (n : nat) :
  (AS ~> fS _ AS) -> list A -> f (list A) _ := _nthTraversal' n f fS func app.

Instance _nthTraversal_Proper {f fS func} {app : @Applicative f fS func} A (AS : Setoid A) : Proper (equiv ==> equiv ==> equiv ==> equiv) (_nthTraversal).
Proof.
  autounfold. intros. unfold _nthTraversal, _nthTraversal'. matchequiv. rewrite H. clear x H. generalize y H1. clear y H1. apply list_ind_2 with (l1:=x1) (l2:=y1).
  intros. rewritesr. 
  intros. inversion H1.
  intros. inversion H1.
  intros. inversion H1. induction y.
  unfold listS_update. rewrite H0, H6, H8. reflexivity.
  unfold listS_update. fold listS_update. rewrite H. rewrite H6. reflexivity. auto. rewritesr.
Qed.

Definition nthTraversal {f fS func} {app : @Applicative f fS func} {A} {AS : Setoid A} := injF3 _nthTraversal _.



Fixpoint list_zipWith {A : Type} {AS : Setoid A} {B : Type} {BS : Setoid B}{C : Type} {CS : Setoid C}(f : AS ~> BS ~~> CS) (l1 : list A) (l2 : list B)  :=
  match l1 , l2 with
    | nil , _ => nil
    | _, nil => nil
    | a1 :: as1 , a2 :: as2 => (f @ a1 @ a2) :: list_zipWith f as1 as2 
  end
.

Instance list_zipWith_Proper {A : Type} {AS : Setoid A} {B : Type} {BS : Setoid B}{C : Type} {CS : Setoid C} : Proper (equiv ==> equiv ==> equiv ==> equiv) (@list_zipWith A _ B _ C _).
Proof.
  autounfold. intros. generalize H0 x1 y1 H1. clear H0 x1 y1 H1. apply list_ind_2 with (l1:=x0) (l2:=y0).
  intros. simpl. auto.
  intros. inversion H1.
  intros. inversion H1.
  intros. inversion H1. simpl. matchequiv.
  inversion H9.   constructor. auto. auto.
rewritesr.
  apply H0. auto. auto.
Qed.

Definition list_zipWithS {A : Type} {AS : Setoid A} {B : Type} {BS : Setoid B}{C : Type} {CS : Setoid C} := injF3 (@list_zipWith A _ B _ C _) _.

Fixpoint list_zipWith' {A : Type} {AS : Setoid A} {B : Type} {BS : Setoid B} (f : AS ~> BS ~~> AS) (l1 :list A) (l2 : list B)  :=
  match l1 , l2 with
    | nil , _ => nil
    | _, nil => l1
    | a1 :: as1 , a2 :: as2 => (f @ a1 @ a2) :: list_zipWith' f as1 as2 
  end
.

Instance list_zipWith'_Proper {A : Type} {AS : Setoid A}{B : Type} {BS : Setoid B} : Proper (equiv ==> equiv ==> equiv ==> equiv) (@list_zipWith' A _ B _).
Proof.
  autounfold. intros. generalize H0 x1 y1 H1. clear H0 x1 y1 H1. apply list_ind_2 with (l1:=x0) (l2:=y0).
  intros. simpl. auto.
  intros. inversion H1.
  intros. inversion H1.
  intros. inversion H1. simpl. matchequiv.
  constructor. auto. auto.
  inversion H9. constructor. rewritesr.
  apply H0. auto. auto.
Qed.


Definition list_zipWithS' {A : Type} {AS : Setoid A} {B : Type} {BS : Setoid B} := injF3 (@list_zipWith' A _ B _) _.

Definition nth_errorS {A : Type} {AS : Setoid A} : listS AS ~> natS ~~> maybeS AS := injF2 (@nth_error A) _.

Definition nth_errorS' {A : Type} {AS : Setoid A} := flipS @ (@nth_errorS A AS).

Lemma list_zipWith'_cons : forall {A : Type} {AS : Setoid A}{B : Type} {BS : Setoid B}(a : A) (la : list A) (b: B) (lb: list B)(f : AS ~> BS ~~> AS), list_zipWith' f (a::la)(b::lb) = (f @ a @ b) :: list_zipWith' f la lb.

Proof.
  intros. reflexivity.
Qed.


(* infinite list with finite nonrepeating prefix and an infinitely repeating element *)

Inductive lista A : Type := listaCons : A -> list A -> @lista A.

Fixpoint list_all {A} {AS : Setoid A} (l : list A) (a : A) :=
  match l with
    | nil => True
    | a' :: l' => a' == a /\ list_all l' a
  end.

Fixpoint lista_equiv0 {A} {AS : Setoid A} (a1 a2 : A) (l1 l2 : list A) :=
  match l1, l2 with
    | nil, l2' => a1 == a2 /\ list_all l2' a1
    | a1' :: l1', nil =>
      a1' == a2 /\ lista_equiv0 a1 a2 l1' nil
    | a1' :: l1', a2' :: l2' =>
      a1' == a2' /\ lista_equiv0 a1 a2 l1' l2'
  end
.
Lemma lista_equiv0_equiv : forall A (AS : Setoid A) (a1 a2 : A) (l1 l2 : list A), lista_equiv0 a1 a2 l1 l2 -> a1 == a2.
Proof.
  intros. generalize H. clear H. apply list_ind_2 with (l1:=l1)(l2:=l2).
  simpl. tauto.
  intros. simpl in *. tauto.
  intros. simpl in *. tauto.
  intros. simpl in *. tauto.
Qed.

                               
Definition lista_equiv {A} {AS : Setoid A} (l1 l2 : lista A) :=
  match l1, l2 with
    | listaCons _ a1 ll1, listaCons _ a2 ll2 => lista_equiv0 a1 a2 ll1 ll2
  end.

Instance lista_equiv_Equivalence {A} {AS : Setoid A} : Equivalence (@lista_equiv A AS).
Proof.
  split.
  autounfold. intros. destruct x. simpl. induction l.
  simpl. split. reflexivity. auto.
  simpl. split. reflexivity. auto. 
  autounfold. intros. destruct x,y. simpl in *. generalize H. clear H. apply list_ind_2 with (l1:=l) (l2:=l0).
  intros.   simpl. destruct H. split. symmetry. auto. auto.
  intros.  simpl. simpl in H0. split.  tauto.  apply H. simpl.  tauto.
  intros.  simpl. simpl in H0, H. split. apply H. tauto. split. tauto. apply H. tauto.
  intros. simpl. simpl in H0. split. symmetry. tauto. apply H. tauto.
  autounfold. intros. destruct x,y,z. simpl in *.  generalize l0 H H0. clear H l0 H0. apply list_ind_2 with (l1:=l) (l2:=l1).
  intros. simpl in *. split. transitivity a0. tauto. apply lista_equiv0_equiv with (l1:=l0) (l2:=nil). auto. auto. 
  intros. simpl in *. split. transitivity a0. tauto. apply lista_equiv0_equiv with (l1:=l0) (l2:=a2 :: b). auto. split. destruct l0. simpl in *. transitivity a0. tauto. symmetry. tauto. simpl in *. transitivity a3. symmetry. tauto. tauto. destruct l0.  specialize (H nil). simpl in *.  tauto. specialize (H l0). simpl in *. tauto.
  intros. simpl in *. split. destruct l0. simpl in *. transitivity a0. tauto. tauto. transitivity a3. tauto. simpl in *. tauto. destruct l0. simpl in *. apply H with (l0:=nil).  tauto. auto. simpl in *. apply H with (l0:=l0). tauto. tauto.
  intros. simpl in *. split. destruct l0. simpl in *. transitivity a0. tauto. symmetry. tauto. simpl in *. transitivity a3. tauto. tauto. destruct l0. simpl in *. apply H with (l0 := nil). tauto. simpl. tauto. simpl in *. apply H with (l0:=l0). tauto. tauto.
Qed.

Instance listaS {A} (AS : Setoid A) : Setoid (lista A) :=
  {
    equiv := lista_equiv
  }.

Fixpoint lista_update0 {A} {AS : Setoid A} (n:nat) (a0 : A) (l:list A)  (a:A ) {struct n} :  list A :=
  match n, l with
    | 0, [] => [a] 
    | 0, a'::l' => a ::l'
    | S n', [] => a0 :: lista_update0 n' a0 [] a
    | S n', a'::l' => a':: lista_update0 n' a0 l' a
  end.


Instance lista_update0_Proper A (AS : Setoid A): Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) (@lista_update0 A AS).
Proof.
  autounfold. intros. rewrite H.  clear x H. generalize y H1. clear y H1. apply list_ind_2 with (l1:=x1) (l2:=y1).
  intros. induction y.
  simpl.  constructor. auto. auto. 
  simpl.  constructor. auto. auto. 
  intros. inversion H1.
  intros. inversion H1.
  intros. inversion H1. induction y.
  simpl.  constructor.  auto. auto. 
  simpl. constructor. auto. apply H. auto. 
Qed.

Definition lista_update {A} {AS : Setoid A} (n:nat) (l:lista A)  (a:A )  :  lista A :=
  match l with
    | listaCons _ a0 l => listaCons _ a0 (lista_update0 n a0 l a)
  end.

Hint Unfold lista_update.

Instance listaCons_Proper A (AS : Setoid A): Proper (equiv ==> equiv ==> equiv) (@listaCons A).
Proof.
  autounfold. intros. simpl. generalize H0. clear H0. apply list_ind_2 with (l1:=x0) (l2:=y0).
  simpl. auto.
  intros. inversion H1.
  intros. inversion H1.
  intros. inversion H1. simpl. tauto.
Qed.

Definition listaConsS {A} {AS : Setoid A} := injF2 (@listaCons A) _.
Lemma listaCons_equiv : forall A (AS : Setoid A) (a1 a2 : A) (l1 l2 : list A), listaCons _ a1 l1 == listaCons _ a2 l2 -> a1 == a2.
Proof.
  intros. generalize H. clear H. apply list_ind_2 with (l1:=l1)(l2:=l2).
  simpl. tauto.
  intros. apply H. simpl in *. tauto.
  intros. apply H. simpl in *. tauto.
  intros. apply H. simpl in *. tauto.
Qed.

Instance lista_update_Proper A (AS : Setoid A): Proper (equiv ==> equiv ==> equiv ==> equiv) (@lista_update A AS).
Proof.
  autounfold. intros. destruct x0, y0.  rewrite H, H1. clear x H x1 H1. generalize y H0. clear y H0. apply list_ind_2 with (l1:=l) (l2:=l0).
  intros. induction y.
  simpl in *.   split. reflexivity. tauto. 
  simpl in *.  tauto. 
  intros. destruct y.
  simpl in *. split. reflexivity. tauto.
  simpl. simpl in H0.  split.   symmetry. tauto. apply H.  simpl. tauto.
  intros. destruct y.
  simpl in *. split. reflexivity. tauto.
  simpl. simpl in H0. split. tauto. simpl in *. apply H. tauto. 
  intros. destruct y.
  simpl in *. split. reflexivity. tauto.
  simpl in *. split. tauto. apply H. tauto.
Qed.

Definition lista_updateS {A} {AS : Setoid A} := injF3 (@lista_update A AS) _.

Fixpoint lista_truncate0 {A} {AS : Setoid A} n  (a0 : A) (l : list A) :=
  match n, l with
    | 0, _ => []
    | S n', [] => a0 :: lista_truncate0 n' a0 []
    | S n', a' :: l' => a' :: lista_truncate0 n' a0 l'
  end
.

Definition lista_truncate {A} {AS : Setoid A} n (a : A) (la : lista A) :=
  match la with
    | listaCons _ a0 l => listaCons _ a (lista_truncate0 n a0 l)
  end
.

Instance lista_truncate_Proper A (AS : Setoid A): Proper (equiv ==> equiv ==> equiv ==> equiv) (@lista_truncate A AS).
Proof.
  autounfold. intros. rewrite H. clear x H. destruct x1, y1. generalize y H1. clear y H1. apply list_ind_2 with (l1:=l) (l2:=l0).
  intros. simpl in H1. induction y.
  simpl. tauto.
  simpl. tauto. 
  intros. destruct y.
  simpl in *. split. eauto using lista_equiv0_equiv. auto.
  simpl in *. split. symmetry.  tauto. apply H. tauto.
  intros. destruct y.
  simpl in *. split. eauto using lista_equiv0_equiv. auto.
  simpl in *. split. tauto. apply H. tauto. 
  intros. destruct y.
  simpl in *. split. eauto using lista_equiv0_equiv. auto.
  simpl in *. split. tauto. apply H. tauto.
Qed.

Definition lista_truncateS {A} {AS : Setoid A} := injF3 (@lista_truncate A AS) _.

Lemma lista_equiv_lista_truncate: forall A (AS : Setoid A) n (a1 a2:A) (l1 l2 :lista A),
                                       lista_truncate n a1 l1 == lista_truncate n a1 l2 ->
                                       lista_truncate n a2 l1 == lista_truncate n a2 l2.
Proof.
  destruct l1, l2. generalize l l0. clear l l0. induction n.
  simpl. intros. split. reflexivity. auto.
  intros. destruct l, l0.
  simpl in *. split. tauto. apply IHn. tauto.
  simpl in *. split. tauto. apply IHn. tauto.
  simpl in *. split. tauto. apply IHn. tauto.
  simpl in *. split. tauto. apply IHn. tauto.
Qed.

Lemma lista_truncate_lista_update  :
  forall {A} {AS : Setoid A} n (a : A)(a0:A )(n0:nat) (l1 l2:lista A),
    lista_truncate n a l1 == lista_truncate n a l2 ->
    lista_truncate n a (lista_updateS @ n0 @ l1 @ a0) == lista_truncate n a (lista_updateS @ n0 @ l2 @ a0).
Proof.
  destruct l1, l2. generalize n n0. clear n n0. apply list_ind_2 with (l1:=l) (l2:=l0).
  intros. destruct n.
  simpl. auto.
  destruct H. rewrite H. reflexivity. 
  intros. destruct n.
  simpl. auto.
  destruct H0. destruct n0.
  simpl. split. reflexivity. auto.
  simpl. split. auto. apply H. auto.
  intros. destruct n.
  simpl. auto.
  destruct H0. destruct n0.
  simpl.  split. reflexivity. auto.
  simpl. split. auto. apply H. auto.
  intros. destruct n.
  simpl. auto.
  destruct H0. destruct n0.
  simpl. split. reflexivity. auto.
  simpl. split. auto. apply H. auto.
Qed.

Fixpoint lista_zipWith0_right {A : Type} {AS : Setoid A} {B : Type} {BS : Setoid B} (f : AS ~> BS ~~> AS) (a : A)  (lb : list B) :=
  match lb with
    | [] => []
    | b' :: lb' => (f @ a @ b') :: lista_zipWith0_right f a lb'
  end
.

Fixpoint lista_zipWith0 {A : Type} {AS : Setoid A} {B : Type} {BS : Setoid B} (f : AS ~> BS ~~> AS) (a : A) (la : list A) (b : B) (lb : list B) :=
  match la, lb with
    | [] , _ => lista_zipWith0_right f a lb
    | a' :: la', [] => (f @ a' @ b) :: lista_zipWith0 f a la' b []
    | a' :: la', b' :: lb' => (f @ a' @ b') :: lista_zipWith0 f a la' b lb'
  end
.
Definition lista_zipWith {A : Type} {AS : Setoid A} {B : Type} {BS : Setoid B} (f : AS ~> BS ~~> AS) (la : lista A) (lb : lista B) :=
  match la, lb with
    | listaCons _ a la' , listaCons _ b lb' => listaCons _ (f @ a @ b) (lista_zipWith0 f a la' b lb')
  end
.


Instance lista_zipWith_Proper {A : Type} {AS : Setoid A}{B : Type} {BS : Setoid B} : Proper (equiv ==> equiv ==> equiv ==> equiv) (@lista_zipWith A _ B _).
Proof.
  autounfold. intros. destruct x0,y0,x1,y1. generalize H0 l1 l2 H1. clear H0 l1 l2 H1. apply list_ind_2 with (l1:=l) (l2:=l0).
  - intros. destruct H0. unfold lista_zipWith.   simpl. generalize H1. clear H1. apply list_ind_2 with (l1:=l1) (l2:=l2).
    + simpl. split. destruct H1. rewritesr. auto.
    + intros. simpl in H1, H3. split. tauto. split.  destruct H3 as [? [? ?]]. rewritesr. tauto.
    + intros. simpl in H1, H3. split. destruct H3. rewritesr. tauto.
    + intros. simpl in H1, H3. split. destruct H3. rewritesr. tauto.
  - intros. destruct l1, l2.
    + simpl in H0, H1, H2. destruct H1 as [? [? ?]]. destruct H2. split. rewritesr. split. rewritesr. clear l l0 a1 H0 H1 H3 H5. induction b1.
      * auto.
      * simpl. destruct H4. split. rewritesr. apply IHb1. auto.
    + simpl in H0, H1, H2. destruct H1 as [? [? ?]], H2 as [? [? ?]]. split. rewritesr. split. rewritesr. clear l l0 a1 H0 H3 H5. generalize H4 H6. clear H4 H6. apply list_ind_2' with (l1:=b1) (l2:=l2).
      * simpl.  auto.
      * intros. destruct H6. split. rewritesr. auto.
      * intros. destruct H4. split. rewritesr. auto.
      * intros. destruct H4, H6. split. rewritesr. auto.
    + simpl in H0, H1, H2. destruct H1 as [? [? ?]], H2. split. rewritesr. apply H0. tauto. auto. 
    + simpl in H0, H1, H2. destruct H1 as [? [? ?]], H2. split. rewritesr. apply H0. tauto. auto.
  - intros. destruct l1, l2.
    + simpl in H0, H1, H2. destruct H1, H2. split. rewritesr. apply (H0 H3 [] []). simpl. auto. 
    + simpl in H0, H1, H2. destruct H1, H2 as [? [? ?]]. split. rewritesr. apply H0. auto. simpl. auto. 
    + simpl in H0, H1, H2. destruct H1, H2. split. rewritesr. apply (H0 H3 l1 []). auto. 
    + simpl in H0, H1, H2. destruct H1, H2. split. rewritesr. apply H0. auto. auto.
  - intros. destruct l1, l2.
    + simpl in H0, H1, H2. destruct H1, H2. split. rewritesr. apply H0. auto. simpl. auto. 
    + simpl in H0, H1, H2. destruct H1, H2 as [? [? ?]]. split. rewritesr. apply H0. auto. simpl. auto.
    + simpl in H0, H1, H2. destruct H1, H2. split. rewritesr. apply H0. auto.  auto.
    + simpl in H0, H1, H2. destruct H1, H2. split. rewritesr. apply H0. auto. auto.
Qed.


Definition lista_zipWithS {A : Type} {AS : Setoid A} {B : Type} {BS : Setoid B} := injF3 (@lista_zipWith A _ B _) _.


Definition lista_map  {A : Type} {AS : Setoid A} {B : Type} {BS : Setoid B} (f : AS ~> BS) (la : lista A) :=
  match la with
    | listaCons _ a la' => listaCons _ (f @ a) (mapS @ f @ la')
  end
.

Instance lista_map_Proper {A : Type} {AS : Setoid A}{B : Type} {BS : Setoid B} : Proper (equiv ==> equiv ==> equiv) (@lista_map A _ B _).
Proof.
  autounfold. intros. destruct x0,y0. unfold lista_map.  rewrite H. clear x H.  generalize H0 . clear H0 . apply list_ind_2 with (l1:=l) (l2:=l0).
  - intros. destruct H0. rewritesr.
  - intros. destruct H0, H1. split. rewritesr. split. rewritesr. simpl in H. apply H. tauto.
  - intros. destruct H0. split. rewritesr. simpl in H. apply H. auto. 
  - intros. destruct H0. split. rewritesr. simpl in H. apply H. auto.  
Qed.

Definition lista_mapS  {A : Type} {AS : Setoid A}{B : Type} {BS : Setoid B}:= injF2 (@lista_map A AS B BS) _.

Definition lista_nth {A : Type} {AS : Setoid A} n (l : lista A) :=
  match l with
    | listaCons _ a l' => nth n l' a
  end
.
Instance lista_nth_Proper {A : Type} {AS : Setoid A} : Proper (equiv ==> equiv ==> equiv) lista_nth.
Proof.
  autounfold. intros. destruct x0, y0. simpl. rewrite H. clear x H. generalize y H0. clear y H0. apply list_ind_2 with (l1:=l) (l2:=l0).
  - simpl. destruct y. tauto. tauto.
  - intros.  destruct H0. destruct H1. simpl. destruct y. rewritesr. rewrite <- H. simpl. destruct y. reflexivity. reflexivity. simpl. auto.
  - intros.  destruct H0. simpl. destruct y. rewritesr. rewrite H. simpl. destruct y. reflexivity. reflexivity. simpl. auto.
  - intros.  destruct H0. simpl. destruct y. rewritesr. apply H. simpl.  auto.
Qed.

Definition lista_nthS {A : Type} {AS : Setoid A} := injF2 (@lista_nth A AS) _.

Definition _listaNthLens' {A : Type} {AS : Setoid A} (n : nat) : _Lens' (lista A) A.
  unfold _Lens'. intros. refine (lista_updateS @ n @ X0 <$> (X @ (lista_nthS @ n @ X0))).
Defined.

Definition _listaNthLens {f fS} {func : @Functor f fS} {A : Type} {AS : Setoid A} (n : nat) :=
  @_listaNthLens' A AS n f fS func.

Instance _listaNthLens_Proper {f fS} {func : @Functor f fS} {A : Type} {AS : Setoid A}(n : nat): Proper (equiv ==> equiv ==> equiv ) (@_listaNthLens f fS func A AS n).
Proof.
  autounfold. intros. unfold _listaNthLens, _listaNthLens'. rewritesr.
Qed.

Definition listaNthLens {f fS} {func : @Functor f fS} {A} {AS : Setoid A} (n : nat) :=
  injF2 (@_listaNthLens f fS func A AS n) _.

Fixpoint list_findn {A : Type} {AS : Setoid A} (p : AS ~> boolS) (a : A) (l : list A)  (n : nat) : maybe nat :=
  match l with
    | [] => if p @ a then Some n else None
    | a' :: l' => if p @ a' then Some n else list_findn p a l' (S n)
  end
.

Definition lista_find {A : Type} {AS : Setoid A} (p : AS ~> boolS) (l : lista A) : maybe nat :=
  match l with
    | listaCons _ a' l' => list_findn p a' l' 0
  end
.

Instance lista_find_Proper {A : Type} {AS : Setoid A}: Proper (equiv ==> equiv ==> equiv ) (@lista_find A AS).
Proof.
  autounfold. intros. destruct x0, y0.  unfold lista_find. generalize 0 H0. clear H0. apply list_ind_2 with (l1:=l) (l2:=l0).
  - intros. destruct H0.  match goal with
      | |- ?a == ?b => simpl a; simpl b
    end. matchequiv.  inversion H2. inversion H2. 
  - intros. destruct H1 as [? [? ?]].
    match goal with
      | |- ?a == ?b => simpl a; simpl b
    end. rewrite H , H2. assert (y @ a = true \/ y @ a = false). destruct (y @ a). tauto. tauto. destruct H4. rewrite H4. reflexivity.  rewrite H4. rewrite <- H0. simpl. rewrite <- H in H4. rewrite H4. auto. simpl.   auto.
  - intros. destruct H1 as [? ?].
    match goal with
      | |- ?a == ?b => simpl a; simpl b
    end. rewrite H , H1. assert (y @ a0 = true \/ y @ a0 = false). destruct (y @ a0). tauto. tauto. destruct H3. rewrite H3. reflexivity.  rewrite H3. rewrite H0. simpl. rewrite H3. auto. simpl.   auto.
  - intros. destruct H1 as [? ?].
    match goal with
      | |- ?a == ?b => simpl a; simpl b
    end. rewrite H , H1. assert (y @ c = true \/ y @ c = false). destruct (y @ c). tauto. tauto. destruct H3. rewrite H3. reflexivity.  rewrite H3. apply H0. auto. 
Qed.

Definition lista_findS {A} {AS : Setoid A} :=
  injF2 (@lista_find A AS) _.


Fixpoint list_findan {A : Type} {AS : Setoid A} (d : forall a a' : A, {a==a'} + {~a==a'}) (a : A) (l : list A)  (n : nat) :  nat :=
  match l with
    | [] =>  n
    | a' :: l' => if d a a' then  n else list_findan d a l' (S n)
  end
.

Definition lista_finda {A : Type} {AS : Setoid A} (d : forall a a' : A, {a==a'} + {~a==a'}) (l : lista A) :  nat :=
  match l with
    | listaCons _ a' l' => list_findan d a' l' 0
  end
.

Instance lista_finda_Proper {A : Type} {AS : Setoid A} d: Proper (equiv ==> equiv ) (@lista_finda A AS d).
Proof.
  autounfold. intros. destruct x, y.  unfold lista_finda. generalize 0 H. clear H. apply list_ind_2 with (l1:=l) (l2:=l0).
  - intros. simpl. auto. 
  - intros. destruct H0 as [? [? ?]].
    simpl. destruct (d a0 a1). reflexivity.  rewrite H1 in n0. symmetry in H0. tauto.
    
  - intros. destruct H0 as [? ?].
    simpl. destruct (d a a1). reflexivity.  pose (listaCons_equiv _ _ a a0 b [] H1). rewrite H0 in n0. tauto.
  - intros. destruct H0 as [? ?].
    match goal with
      | |- ?a == ?b => simpl a; simpl b
    end. pose (listaCons_equiv _ _ a a0 b d0 H1). destruct (d a a1), (d a0 c). reflexivity. rewrite <- e, <- H0 in n0. tauto. rewrite <- e, <- H0 in e0. tauto. apply H. auto. 
Qed.

Definition lista_findaS {A} {AS : Setoid A} d :=
  injF (@lista_finda A AS d) _.

Definition lista_repeat {A : Type} {AS : Setoid A} (a : A) := listaCons _ a [].
Instance lista_repeat_Proper {A : Type} {AS : Setoid A} : Proper (equiv ==> equiv ) (@lista_repeat A AS).
Proof.
  autounfold. intros. simpl. auto.
Qed.

Definition lista_repeatS {A : Type} {AS : Setoid A} := injF (@lista_repeat A AS) _.

Fixpoint list_filter_index {A : Type} {AS : Setoid A} (p : AS ~> boolS) (l : list A) n : list nat :=
  match l with
    | [] => []
    | a' :: l' => if p @ a' then n :: list_filter_index p l' (S n) else list_filter_index p l' (S n)
  end
.

Definition lista_filter_index {A : Type} {AS : Setoid A} (p : AS ~> boolS) (l : lista A) : list nat :=
  match l with
    | listaCons _ a' l' => if (p @ a') then [] else list_filter_index p l' 0
  end
.

Instance lista_filter_index_Proper {A : Type} {AS : Setoid A}: Proper (equiv ==> equiv ==> equiv ) (@lista_filter_index A AS).
Proof.
  autounfold. intros. destruct x0, y0.  unfold lista_filter_index. generalize 0 H0. clear H0. apply list_ind_2 with (l1:=l) (l2:=l0).
  - intros. destruct H0. simpl. matchequiv.  
  - intros. destruct H1 as [? [? ?]].
    match goal with
      | |- ?a == ?b => simpl a; simpl b
    end. rewrite H , <- H1, H2. assert (y @ a = true \/ y @ a = false). destruct (y @ a). tauto. tauto. destruct H4. rewrite H4. reflexivity.  rewrite H4. rewrite <- H in H4. rewrite H4 in H0. rewrite H, H1 in H4. rewrite H4 in H0. rewrite <- H0. simpl. auto.  simpl.   auto.
  - intros. destruct H1 as [? ?].
    match goal with
      | |- ?a == ?b => simpl a; simpl b
    end.  pose (listaCons_equiv _ _ a a0 b [] H2).   assert (x @ a = true \/ x @ a = false). destruct (x @ a). tauto. tauto. destruct H3. rewrite H3. rewrite H, e in H3. rewrite H3. reflexivity.  rewrite H3. rewrite e, <- H1 in H3. rewrite H3. rewrite H1 , <- e in H3. rewrite H3 in H0. rewrite H, e in H3. rewrite H3 in H0. rewrite H0. simpl. rewrite H3. auto. simpl.   auto.
  - intros. destruct H1 as [? ?].
    match goal with
      | |- ?a == ?b => simpl a; simpl b
    end.  pose (listaCons_equiv _ _ a a0 b d H2). assert (x @ a = true \/ x @ a = false). destruct (x @ a). tauto. tauto. destruct H3. rewrite H3 in *. rewrite H, e in H3. rewrite H3 in *. auto.   rewrite H3 in *. rewrite H, H1. rewrite H, e in H3. rewrite H3 in *. destruct (y @ c). constructor. reflexivity. apply H0. auto.  apply H0. auto.
Qed.

Definition lista_filter_indexS {A} {AS : Setoid A} :=
  injF2 (@lista_filter_index A AS) _.

Fixpoint list_filter_index' {A : Type} {AS : Setoid A}  (l : list (maybe A)) n : list (nat * A) :=
  match l with
    | [] => []
    | a' :: l' =>
      match a' with
        | Some a' => (n, a') :: list_filter_index'  l' (S n)
        | None => list_filter_index'  l' (S n)
      end
  end
.

Definition lista_filter_index' {A : Type} {AS : Setoid A}  (l : lista (maybe A)) : list (nat * A) :=
  match l with
    | listaCons _ a' l' =>
      match a' with
        | Some _ =>  []
        | None => list_filter_index' l' 0
      end
  end
.

Instance lista_filter_index'_Proper {A : Type} {AS : Setoid A}: Proper (equiv ==> equiv ) (@lista_filter_index' A AS).
Proof.
  autounfold. intros. destruct x, y.  unfold lista_filter_index'. generalize 0 H. clear H. apply list_ind_2 with (l1:=l) (l2:=l0).
  - intros. destruct H. simpl. matchequiv.  
  - intros. destruct H0 as [? [? ?]]. matchequiv.  destruct a. inversion H1. simpl. rewrite <- H. reflexivity. simpl.  auto. 
  - intros. destruct H0.  pose (listaCons_equiv _ _ m m0 b [] H1). matchequiv. destruct a.  inversion H0. simpl.  rewrite H. simpl. reflexivity.   simpl.   auto.
  - intros. destruct H0.  pose (listaCons_equiv _ _ m m0 b d H1). matchequiv. simpl. matchequiv. constructor. simpl in H3. rewritesr. apply H. auto. apply H. auto.
Qed.

Definition lista_filter_indexS' {A} {AS : Setoid A} :=
  injF (@lista_filter_index' A AS) _.

(* partial matrix *)

Inductive matrixp A {AP : Pointed A} : Type := matrixpCons : nat -> lista (option (lista A)) -> matrixp A. 


Existing Instance maybe_Monad.
Existing Instance monadFunctor.
Definition _rows  {A : Type} {AS : Setoid A} {AP : Pointed A} (mat : matrixp A) : lista (maybe (lista A)) := match mat with
                     | matrixpCons _ w rows => lista_mapS @ (fmap @ (lista_truncateS @ w @ point)) @ rows
                   end.


Definition matrixp_equiv {A} {AS : Setoid A}{AP : Pointed A} (m1 m2 : matrixp A) : Prop :=
  match m1, m2 with
    | matrixpCons _ n l, matrixpCons _ n0 l0 =>
      n = n0 /\ _rows m1 == _rows m2
  end.


Hint Unfold matrixp_equiv.

Instance matrixp_equiv_Equivalence {A} {AS : Setoid A} {AP : Pointed A}: Equivalence (matrixp_equiv).
Proof.
  split.
  - autounfold. intros. destruct x. split. auto. reflexivity. 
  - autounfold. intros. destruct x, y. destruct H. split. auto. symmetry. auto. 
  - autounfold. intros. destruct x, y, z. destruct H, H0. split. congruence. transitivity (_rows (matrixpCons A n0 l0)). auto.
auto.
Qed.


Instance matrixpS {A} (AS : Setoid A) {AP : Pointed A} : Setoid (matrixp A) :=
  {
    equiv := matrixp_equiv
  }
.

Instance _rows_Proper A (AS : Setoid A) (AP : Pointed A) : Proper (equiv ==> equiv) (@_rows A AS AP).
Proof.
  autounfold. intros. destruct x, y, l, l0. unfold _rows. inversion H. clear H. rewrite H0 in *. clear n H0. generalize H1. clear H1. apply list_ind_2 with (l1:= l) (l2:=l0).
  - intros. auto.  
  - intros. destruct H1. destruct H1. split. auto. split. auto. apply H. split. auto. auto.
  - intros. destruct H1. split. auto. apply H. auto.
  - intros. destruct H1. split. auto. apply H. auto.
Qed.

Definition rows {A : Type} {AS : Setoid A} {AP : Pointed A} := injF (@_rows A AS AP) _.

Lemma lista_truncate_equiv_equiv : forall A (AS : Setoid A) l1 l2 n (a : A),  l1 == l2 -> lista_truncate n a l1 == lista_truncate n a l2.
Proof.
  intros. generalize n H. clear n H . destruct l1, l2. apply list_ind_2 with (l1:=l) (l2:=l0).
  - simpl. intros. induction n.
    + simpl. split. reflexivity. auto.
    + simpl. tauto.
  - intros. destruct H0.  destruct H1. induction n.
    + simpl. split. reflexivity. auto.
    + simpl. split. symmetry. auto. apply H. simpl. auto. 
  - intros. destruct H0.  induction n.
    + simpl. split. reflexivity. auto.
    + simpl. split. auto. apply H. simpl. auto. 
  - intros. destruct H0.  induction n.
    + simpl. split. reflexivity. auto.
    + simpl. split. auto. apply H. simpl. auto. 
Qed.

Instance matrixpCons_Proper {A : Type} {AS : Setoid A} {AP : Pointed A} : Proper (equiv ==> equiv ==> equiv) (@matrixpCons A AP).
Proof.
  autounfold. intros. split. auto. destruct x0, y0. destruct o, o0.
  - generalize H0. clear H0. apply list_ind_2 with (l1:=l) (l2:=l0).
    + intros. destruct H0. split. rewritesr. auto. 
    + intros. destruct H1. destruct H2. split. apply H0. simpl.  auto. split. rewritesr. apply H0. simpl. auto. 
    + intros. destruct H1. split. rewritesr. apply H0. simpl. auto.
    + intros. destruct H1. split. rewritesr. apply H0. simpl. auto.
  - pose (listaCons_equiv _ _ (Some l1) None l l0 H0). inversion e. 
  - pose (listaCons_equiv _ _ None (Some l1)  l l0 H0). inversion e. 
  - generalize H0. clear H0. apply list_ind_2 with (l1:=l) (l2:=l0).
    + intros. destruct H0. split. rewritesr. auto.
    + intros. destruct H1. destruct H2. split. apply H0. simpl.  auto. split. rewritesr. apply H0. simpl. auto. 
    + intros. destruct H1. split. rewritesr. apply H0. simpl. auto.
    + intros. destruct H1. split. rewritesr. apply H0. simpl. auto.
Qed.

(* read matrix column *)


Definition _readCol {A : Type} {AS : Setoid A} (w n : nat) (l : maybe (lista A)) :=
  if lt_dec n w then
    match l with
      | None => None
      | Some l' => Some (lista_nth n l')
    end
  else
    None.
Lemma _readCol_lista_truncate :
  forall {A : Type} {AS : Setoid A} (w n : nat) (a : A) (l :  lista A),
    _readCol w n (Some l) == _readCol w n (Some (lista_truncate w a l)).

Proof.

  intros. destruct l. unfold _readCol. destruct (lt_dec n w).
  - simpl. generalize w l0 l. clear w l0 l. induction n.
    + intros.  destruct w.
      * inversion l0.
      * destruct l. simpl. reflexivity. simpl. reflexivity. 
    +  intros. destruct w.
       * inversion l0.
       * destruct l. simpl. rewrite <- IHn. simpl. destruct n. reflexivity. reflexivity.
    apply le_S_n. auto.
    simpl. rewrite <- IHn. reflexivity. apply le_S_n.  auto.
  - reflexivity.
Qed.
  
Instance _readCol_Proper {A : Type} {AS : Setoid A} : Proper (equiv ==> equiv ==> equiv ==> equiv) (@_readCol A AS).
Proof.
  autounfold. intros. unfold _readCol. simpl in H, H0. rewrite H, H0. destruct (lt_dec y0 y). matchequiv. destruct l0, l1.  simpl in H1. simpl. clear x H x0 H0. generalize y0 H1 l. clear y0 H1 l. apply list_ind_2 with (l1:=l0)(l2:=l1).
  intros. simpl in *.  destruct y0. tauto. tauto.
  intros. destruct y0. simpl in *. symmetry. tauto. simpl. rewrite <- H. destruct y0.  reflexivity. reflexivity. simpl in *. tauto. apply Nat.lt_le_incl. auto. 
  intros. destruct y0. simpl in *. tauto. simpl. rewrite H. destruct y0.  reflexivity. reflexivity. simpl in *. tauto. apply Nat.lt_le_incl. auto. 
  intros. destruct y0. simpl in *. tauto. simpl. apply H. simpl in *. tauto. apply Nat.lt_le_incl. auto.
  reflexivity. 
Qed.

Definition readCol {A : Type} {AS : Setoid A} := injF3 (@_readCol A AS) _. 

Definition readWholeCol {A} {AS : Setoid A} w n := lista_mapS @ (readCol @ w @ n).

Definition _readMatrixCol {A : Type} {AS : Setoid A} {AP : Pointed A} n mat :=
  match mat with
    | matrixpCons _ w l => readWholeCol w n @ l
  end.
Lemma lista_nth_truncate_equiv : forall A (AS:Setoid A) n0 (a :A) (l1 l2 : lista A) n, lista_truncate n0 a l1 == lista_truncate n0 a l2 -> n < n0 -> lista_nth n l1 == lista_nth n l2.
Proof.
  intros. destruct l1, l2. generalize n n0 H0 H.  clear n n0 H0 H. apply list_ind_2 with (l1:=l) (l2:=l0).
  - simpl. intros. destruct n0. inversion H0. destruct H. destruct n. auto.  auto.
  - intros. simpl in *. destruct n0.  inversion H0. destruct H1. destruct n. auto. rewrite <- H with (n0 := n0). destruct n. reflexivity. reflexivity. apply le_S_n. auto. auto.
  - intros. simpl in *. destruct n0.  inversion H0. destruct H1. destruct n. auto. rewrite H with (n0 := n0). destruct n. reflexivity. reflexivity. apply le_S_n. auto. auto.
  - intros. simpl in *. destruct n0.  inversion H0. destruct H1. destruct n. auto. apply H with (n0 := n0). apply le_S_n. auto. auto.
Qed.

Lemma readCol_truncate_equiv : forall A (AS:Setoid A) (w n : nat) a (l1 l2 : lista A) n, lista_truncate w a l1 == lista_truncate w a l2 -> readCol @ w @ n @ Some l1 == readCol @ w @ n @ Some l2.
Proof.
  intros. simpl. unfold _readCol. destruct (lt_dec n0 w). apply (lista_nth_truncate_equiv _ _ w a). auto. auto. auto.
Qed.

Instance _readMatrixCol_Proper {A} {AS : Setoid A} {AP : Pointed A} : Proper (equiv ==> equiv ==> equiv) (@_readMatrixCol A AS AP).
Proof.
  autounfold. intros. destruct x0, y0. unfold _readMatrixCol. rewrite H. clear x H. destruct H0.  rewrite H in *. clear n H. generalize H0. clear H0. destruct l, l0. destruct o, o0.
  - apply list_ind_2 with (l1:=l)(l2:=l0).
    + intros. destruct H0. simpl in H, H0.   split. apply (readCol_truncate_equiv _ _ n0 y point). auto. auto. 
    + intros. destruct H0. destruct H1. destruct a.
      * split. apply (readCol_truncate_equiv _ _ n0 y point). auto. split. apply (readCol_truncate_equiv _ _ n0 y point). auto. apply H.  split. auto. auto.
      * inversion H1.
    + intros. destruct H0. destruct a.
      * split. apply (readCol_truncate_equiv _ _ n0 y point). auto. apply H.  auto. 
      * inversion H0.
    + intros. destruct H0. destruct a, c.
      * split. apply (readCol_truncate_equiv _ _ n0 y point). auto. apply H.  auto. 
      * inversion H0.
      * inversion H0.
      * split. reflexivity. apply H. auto.
        
  - intros. generalize H0. clear H0. apply list_ind_2 with (l1:=l)(l2:=l0).
    + intros. destruct H0. inversion H. 
    + intros. destruct H0. inversion H0.
    + intros. destruct H0. destruct a.
      * inversion H0.
      * split. reflexivity. apply H. auto.
    + intros. destruct H0. destruct a, c.
      * split. apply (readCol_truncate_equiv _ _ n0 y point). auto. apply H.  auto. 
      * inversion H0.
      * inversion H0.
      * split. reflexivity. apply H. auto.
  - intros. generalize H0. clear H0. apply list_ind_2 with (l1:=l)(l2:=l0).
    + intros. destruct H0. inversion H. 
    + intros. destruct H0. inversion H0.
    + intros. destruct H0. destruct a.
      * split. apply (readCol_truncate_equiv _ _ n0 y point). auto. apply H. auto.
      * inversion H0.
    + intros. destruct H0. destruct a, c.
      * split. apply (readCol_truncate_equiv _ _ n0 y point). auto. apply H.  auto. 
      * inversion H0.
      * inversion H0.
      * split. reflexivity. apply H. auto.
  - apply list_ind_2 with (l1:=l)(l2:=l0).
    + intros. destruct H0. simpl in H, H0.   split. reflexivity. auto. 
    + intros. destruct H0. destruct H1. destruct a.
      * inversion H1.
      * split. reflexivity. split.  reflexivity.  apply H. split.  auto.  auto. 
    + intros. destruct H0. destruct a.
      * inversion H0.
      * split. reflexivity. apply H. auto. 
    + intros. destruct H0. destruct a, c.
      * split. apply (readCol_truncate_equiv _ _ n0 y point). auto. apply H.  auto. 
      * inversion H0.
      * inversion H0.
      * split. reflexivity. apply H. auto.
Qed.

Definition readMatrixCol {A : Type} {AS : Setoid A}{AP: Pointed A} := injF2 (@_readMatrixCol A AS AP) _.

Definition _updateCol {A : Type} {AS : Setoid A} n (l: maybe (lista A)) (a : maybe A) :=
  match l, a with
    | None, _ => None
    | _, None => l
    | Some l', Some a' => Some (lista_updateS @ n @ l' @ a')
  end
.

Instance _updateCol_Proper {A : Type} {AS : Setoid A} : Proper (equiv ==> equiv ==> equiv ==> equiv) (@_updateCol A AS).
Proof.
  autounfold. intros. destruct x0, y0, x1, y1. simpl. simpl in H0, H1. rewrite H, H0, H1. reflexivity. 
  inversion H1.
  inversion H1.
  simpl. auto.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.
  simpl. auto.
  inversion H1.
  inversion H1.
  simpl. auto.
Qed.

Definition updateCol {A : Type} {AS : Setoid A} := injF3 (@_updateCol A AS) _.

Definition updateWholeCol {A : Type} {AS : Setoid A} n : listaS (maybeS (listaS AS)) ~> listaS (maybeS AS) ~~> listaS (maybeS (listaS AS)) :=
  lista_zipWithS @ (updateCol @ n).



Definition _updateMatrixCol {A : Type} {AS : Setoid A} {AP : Pointed A} n mat col  :=
  match mat with
    | matrixpCons _ w l => matrixpCons _ w (updateWholeCol n @ l @ col)
  end.

Hint Unfold _updateMatrixCol.


(*Lemma matrixp_equiv_cons : forall {A : Type} {AS : Setoid A} w (a1 a2 : A) (a b : maybe (list A)) (la lb : list (maybe (list A))), matrixp_equiv0 w (a::la) (b::lb) = lista_equiv w (listaCons a1 a) (listaCons a2 b) /\ matrixp_equiv0 w a1 a2 la lb.

Proof.
  intros. reflexivity.
Qed.*)


Instance _updateMatrixCol_Proper {A} {AS : Setoid A} {AP : Pointed A} : Proper (equiv ==> equiv ==> equiv ==> equiv) (@_updateMatrixCol A AS AP).
Proof.
  autounfold. intros. destruct x0, y0. destruct x1, y1.  destruct l, l0. destruct  H0.   rewrite H, H0, H1 in *.  clear H0 H H1. generalize H2. clear H2. apply (list_ind_3') with (l1:=l) (l2:=l0) (l3:=l2).
  - split. auto. split.
    + destruct o1, o2, o0.
      * simpl. simpl in H2. apply lista_truncate_lista_update. tauto.
      * simpl. simpl in H2. tauto.
      * simpl. simpl in H2.  tauto.
      * simpl. simpl in H2. tauto.
      * simpl. simpl in H2. tauto.
      * simpl. simpl in H2. tauto.
      * simpl. auto.
      * simpl. auto.
    + simpl. auto. 
  - split. auto. split. destruct H2.
    + destruct o1, o2, a. 
      * simpl. simpl in H0. apply lista_truncate_lista_update. auto.
      * simpl. simpl in H0. auto.
      * simpl in H0.  tauto.
      * simpl in H0. tauto.
      * simpl in H0. tauto.
      * simpl in H0. tauto.
      * simpl. auto.
      * simpl. auto.
    + apply H. auto.
  - split. auto. split. destruct H2.
    + destruct o1, o2, o0. 
      * simpl. simpl in H0. apply lista_truncate_lista_update. auto.
      * simpl. simpl in H0. auto.
      * simpl in H0.  tauto.
      * simpl in H0. tauto.
      * simpl in H0. tauto.
      * simpl in H0. tauto.
      * simpl. auto.
      * simpl. auto.
    + split. destruct H2. destruct H1. destruct a, o1, o0. 
      * simpl. simpl in H1. apply lista_truncate_lista_update. auto.
      * simpl. simpl in H1. auto.
      * simpl in H1.  tauto.
      * simpl in H1. tauto.
      * simpl in H1. tauto.
      * simpl in H1. tauto.
      * simpl. auto.
      * simpl. auto.
    * apply H.  destruct H2.  destruct H1. split.  auto. auto.
  - split. auto. split. destruct H2. destruct H1.
    + destruct o1, a, c. 
      * simpl. simpl in H1. symmetry. apply lista_truncate_lista_update. auto.
      * simpl. simpl in H1. symmetry. auto.
      * simpl in H1.  tauto.
      * simpl in H1. tauto.
      * simpl in H1. tauto.
      * simpl in H1. tauto.
      * simpl. auto.
      * simpl. auto.
    + apply H.  destruct H2.  destruct H1. split.  auto. auto.
  - split. auto. split. destruct H2.
    + destruct a, o2, o0. 
      * simpl. simpl in H0. apply lista_truncate_lista_update. auto.
      * simpl. simpl in H0. auto.
      * simpl in H0.  tauto.
      * simpl in H0. tauto.
      * simpl in H0. tauto.
      * simpl in H0. tauto.
      * simpl. auto.
      * simpl. auto.
    + apply H.  destruct H2.  auto.
  - split. auto. split. destruct H2.
    + destruct a, o2, c. 
      * simpl. simpl in H0. apply lista_truncate_lista_update. auto.
      * simpl. simpl in H0. auto.
      * simpl in H0.  tauto.
      * simpl in H0. tauto.
      * simpl in H0. tauto.
      * simpl in H0. tauto.
      * simpl. auto.
      * simpl. auto.
    + apply H.  destruct H2.  auto.
  - split. auto. split. destruct H2.
    + destruct a, c, o0. 
      * simpl. simpl in H0. apply lista_truncate_lista_update. auto.
      * simpl. simpl in H0. auto.
      * simpl in H0.  tauto.
      * simpl in H0. tauto.
      * simpl in H0. tauto.
      * simpl in H0. tauto.
      * simpl. auto.
      * simpl. auto.
    + apply H.  destruct H2.  auto.
  - split. auto. split. destruct H2.
    + destruct a, c, e. 
      * simpl. simpl in H0. apply lista_truncate_lista_update. auto.
      * simpl. simpl in H0. auto.
      * simpl in H0.  tauto.
      * simpl in H0. tauto.
      * simpl in H0. tauto.
      * simpl in H0. tauto.
      * simpl. auto.
      * simpl. auto.
    + apply H.  destruct H2.  auto.
Qed.

Definition updateMatrixCol {A} {AS : Setoid A} {AP : Pointed A} := injF3 (@_updateMatrixCol A AS AP) _.

Definition _matrixColLens' {A} {AS : Setoid A} {AP : Pointed A} (n : nat) : _Lens' (matrixp A) (lista (maybe A)).
  unfold _Lens'. intros. refine (
                              updateMatrixCol @ n @
                                X0
                                <$> (X @ (readMatrixCol @ n @ X0))).
Defined.

Definition _matrixColLens {f fS }{func : @Functor f fS} {A} {AS : Setoid A} {AP : Pointed A} (n : nat) :
  (listaS (maybeS AS) ~> fS _ (listaS (maybeS AS))) -> matrixp A -> f (matrixp A) _ := _matrixColLens' n f fS func.

Instance _matrixColLens_Proper {f fS} {func : @Functor f fS} A (AS : Setoid A) (AP : Pointed A) : Proper (equiv ==> equiv ==> equiv ==> equiv) (_matrixColLens).
Proof.
  autounfold. intros. unfold _matrixColLens, _matrixColLens'. rewritesr. 
Qed.

Definition matrixColLens {f fS} {func : @Functor f fS} {A} {AS : Setoid A} {AP : Pointed A} := injF3 _matrixColLens _.



Definition _width  {A : Type} {AS : Setoid A} {AP : Pointed A} (mat : matrixp A) : nat.
  simple refine (  match mat with
                     | matrixpCons _ w _ => w
                   end)
.
Defined.

Instance _width_Proper A (AS : Setoid A) AP : Proper (equiv ==> equiv) (@_width A AS AP).
Proof.
  autounfold. intros. destruct x,y. destruct H. simpl. auto.
Qed.

Definition width {A : Type} {AS : Setoid A} {AP} := injF (@_width A AS AP) _.

Definition matrixpConsS {A : Type} {AS : Setoid A} {AP : Pointed A} := injF2 (matrixpCons A) _.

Definition _matrixWidthLens' {A : Type} {AS : Setoid A} {AP : Pointed A}  : _Lens' (matrixp A) nat.
  unfold _Lens'. intros. refine (flipS @ matrixpConsS @ (rows @ X0) <$> (X @ (width @ X0))).
Defined.

Definition _matrixWidthLens {f fS} {func : @Functor f fS} {A : Type} {AS : Setoid A} {AP : Pointed A}  :=
  @_matrixWidthLens' A AS AP f fS func.

Instance _matrixWidthLens_Proper {f fS} {func : @Functor f fS} {A : Type} {AS : Setoid A}{AP: Pointed A}: Proper (equiv ==> equiv ==> equiv ) (@_matrixWidthLens f fS func A AS AP).
Proof.
  autounfold. intros. unfold _matrixWidthLens, _matrixWidthLens'. rewritesr.
Qed.

Definition matrixWidthLens {f fS} {func : @Functor f fS} {A} {AS : Setoid A} {AP: Pointed A} :=
  injF2 (@_matrixWidthLens f fS func A AS AP ) _.

Definition _matrixRowsLens' {A : Type} {AS : Setoid A} {AP : Pointed A}  : _Lens' (matrixp A) (lista (maybe (lista A))).
  unfold _Lens'. intros. refine (matrixpConsS @ (width @ X0) <$> (X @ (rows @ X0))).
Defined.

Definition _matrixRowsLens {f fS} {func : @Functor f fS} {A : Type} {AS : Setoid A} {AP : Pointed A}  :=
  @_matrixRowsLens' A AS AP f fS func.

Instance _matrixRowsLens_Proper {f fS} {func : @Functor f fS} {A : Type} {AS : Setoid A} {AP : Pointed A} : Proper (equiv ==> equiv ==> equiv ) (@_matrixRowsLens f fS func A AS AP).
Proof.
  autounfold. intros. unfold _matrixRowsLens, _matrixRowsLens'. rewritesr.
Qed.

Definition matrixRowsLens {f fS} {func : @Functor f fS} {A} {AS : Setoid A} {AP : Pointed A}  :=
  injF2 (@_matrixRowsLens f fS func A AS AP ) _.

Require Import MaybeLens.
Definition matrixRowTraversal {f fS func} {app : @Applicative f fS func} {A} {AS : Setoid A} {AP : Pointed A}(n : nat) :=
  matrixRowsLens ∘ listaNthLens n ∘ maybePrism. 

Definition matrixCellTraversal {f fS func} {app : @Applicative f fS func} {A} {AS : Setoid A} {AP:Pointed A}(m n : nat) :=
  matrixRowTraversal m ∘ listaNthLens n.

