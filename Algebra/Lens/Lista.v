Require Import Algebra.Functor Algebra.Applicative Algebra.SetoidCat Algebra.ListUtils Algebra.PairUtils Algebra.Maybe Algebra.SetoidUtils Algebra.Monad Algebra.Maybe Tactics Utils Algebra.Pointed FoldableFunctor Monoid MonoidUtils.

Require Import SetoidClass List Coq.Classes.RelationClasses Coq.Arith.PeanoNat Coq.Arith.Compare_dec Coq.Arith.Lt Coq.Arith.Le Basics.

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

Lemma list_update_list_update: forall
  (A : Type)
  (AS : Setoid A)
  n
  a c
  (l : list A),  (list_update' n (list_update' n l a) c )  == list_update' n l c .
Proof.
  intros.  simpl. apply nat_list_ind_2 with (l1:=n) (l2:=l).
    - simpl. reflexivity. 
    - intros. simpl in *. reflexivity. 
    - intros. simpl in *. reflexivity. 
    - intros. simpl in *. constructor ; [reflexivity | auto].
  
Qed.


Lemma list_update_list_nth: forall
  (A : Type)
  (AS : Setoid A)
  n a
  (l : list A),
                              nth_error l n == Some a ->
                              (list_update' n l a)  == l.
Proof.
  intros. generalize H. clear H.  apply nat_list_ind_2 with (l1:=n) (l2:=l).
  - simpl. reflexivity. 
  - intros.  simpl. constructor. simpl in H0.  symmetry. auto. reflexivity.
  - intros. simpl in *. reflexivity. 
  - intros. simpl in *. constructor. reflexivity. auto.  
Qed.

Lemma list_nth_list_update: forall
  (A : Type)
  (AS : Setoid A)
  n a a'
  (l : list A),
                nth_error l n = Some a'
               ->
                              nth_error (list_update' n l a) n = Some a.
Proof.
  intros. generalize H. clear H.  apply nat_list_ind_2 with (l1:=n) (l2:=l).
  - simpl. intros. inversion H. 
  - intros.  simpl.  reflexivity.
  - intros. simpl in *. inversion H0. 
  - intros. simpl in *. apply H. auto. 
Qed.

Lemma list_nth_list_update_diff_index: forall
  (A : Type)
  (AS : Setoid A)
  n n' a
  (l : list A), 
  n <> n' ->nth_error (list_update' n l a) n' = nth_error l n'.
Proof.
  intros.  generalize H a. clear H. apply nat_list_ind_4 with (l1:=n) (l2:=n')(l3:=l).
  - intros. simpl. auto.
  - intros. simpl. auto.
  - intros. destruct H0. auto. 
  - intros. destruct H0. auto. 
  - intros. simpl. auto. 
  - intros. simpl. auto.
  - intros. simpl. auto.
  - intros. simpl. auto.
  - intros. simpl. auto. 
  - intros. simpl. auto.
  - intros. simpl. auto.
  - intros. simpl. auto.
  - intros. simpl. auto. 
  - intros. simpl. auto.
  - intros. simpl. auto.
  - intros. simpl. auto.
  - exact [].
Qed.

(* infinite list with finite nonrepeating prefix and an infinitely repeating element *)

Inductive lista A : Type := listaCons : list A -> @lista A.

Fixpoint list_all {A} {AS : Setoid A} {AP : Pointed A} (l : list A) :=
  match l with
    | nil => True
    | a' :: l' => a' == point /\ list_all l'
  end.

Fixpoint lista_equiv0 {A} {AS : Setoid A} {AP : Pointed A} (l1 l2 : list A) :=
  match l1, l2 with
    | nil, l2' => list_all l2'
    | a1' :: l1', nil =>
      a1' == point /\ lista_equiv0 l1' nil
    | a1' :: l1', a2' :: l2' =>
      a1' == a2' /\ lista_equiv0 l1' l2'
  end
.

Instance lista_equiv0_Reflexive A AS AP : Reflexive (@lista_equiv0 A AS AP).
Proof.
  autounfold. intro. induction x.
  reflexivity.
  split. reflexivity. auto.
Qed.
                               
Definition lista_equiv {A} {AS : Setoid A} {AP : Pointed A} (l1 l2 : lista A) :=
  match l1, l2 with
    | listaCons _  ll1, listaCons _  ll2 => lista_equiv0  ll1 ll2
  end.

Instance lista_equiv_Equivalence {A} {AS : Setoid A} {AP : Pointed A} : Equivalence (@lista_equiv A AS AP).
Proof.
  split.
  autounfold. intros. destruct x. simpl. induction l.
  simpl. auto.
  simpl. split. reflexivity. auto. 
  autounfold. intros. destruct x,y. simpl in *. generalize H. clear H. apply list_ind_2 with (l1:=l) (l2:=l0).
  intros.   simpl.  auto.
  intros.  simpl. simpl in H0. tauto. 
  intros.  simpl. simpl in H0, H. tauto. 
  intros. simpl. simpl in H0. split. symmetry. tauto. tauto. 
  autounfold. intros. destruct x,y,z. simpl in *.  generalize H H0. clear H H0. apply list_ind_3 with (l1:=l) (l2:=l0) (l3:=l1).
  intros. simpl in *. auto.
  intros. auto.
  intros. reflexivity.
  intros. destruct H0, H1. split.  transitivity a. symmetry. auto. auto. apply H. auto. auto.
  intros. auto.
  intros. destruct H0, H1. split. transitivity point. auto. symmetry. auto. apply H. auto. auto.
  intros. destruct H0, H1. split. transitivity c. auto. auto. apply H. auto. auto.
  intros. destruct H0, H1. split. transitivity c. auto. auto. apply H. auto. auto.
Qed.

Instance listaS {A} (AS : Setoid A){AP : Pointed A} : Setoid (lista A) :=
  {
    equiv := lista_equiv
  }.

Fixpoint lista_update0 {A} {AS : Setoid A} {AP : Pointed A} (n:nat) (l:list A)  (a:A ) {struct n} :  list A :=
  match n, l with
    | 0, [] => [a] 
    | 0, a'::l' => a ::l'
    | S n', [] => point  :: lista_update0 n'  [] a
    | S n', a'::l' => a':: lista_update0 n'  l' a
  end.


Instance lista_update0_Proper A (AS : Setoid A) (AP : Pointed A): Proper (equiv ==> equiv ==> equiv ==> equiv) (@lista_update0 A AS AP).
Proof.
  autounfold. intros. rewrite H.  clear x H. generalize y H0. clear y H0. apply list_ind_2 with (l1:=x0) (l2:=y0).
  intros. induction y.
  simpl.  constructor. auto. auto. 
  simpl.  constructor. reflexivity. auto. 
  intros.  inversion H0.
  intros. inversion H0.
  intros. inversion H0. induction y.
  simpl.  constructor.  auto. auto. 
  simpl. constructor. auto. apply H. auto. 
Qed.

Definition lista_update {A} {AS : Setoid A} {AP : Pointed A} (n:nat) (l:lista A)  (a:A )  :  lista A :=
  match l with
    | listaCons _  l => listaCons _  (lista_update0 n  l a)
  end.

Hint Unfold lista_update.


Instance lista_update_Proper A (AS : Setoid A) (AP : Pointed A): Proper (equiv ==> equiv ==> equiv ==> equiv) (@lista_update A AS AP).
Proof.
  autounfold. intros. destruct x0, y0.  rewrite H. clear x H. generalize y H0. clear y H0. apply list_ind_2 with (l1:=l) (l2:=l0).
  intros. induction y.
  simpl in *.   split. auto. auto. 
  simpl in *.  split. reflexivity. auto. 
  intros. destruct y.
  simpl in *. split. auto.  tauto.
  simpl. simpl in H0.  split.   symmetry. tauto. apply H.  simpl. tauto.
  intros. destruct y.
  simpl in *. split. auto.  tauto.
  simpl. simpl in H0. split. tauto. simpl in *. apply H. tauto. 
  intros. destruct y.
  simpl in *. split. auto.  tauto.
  simpl in *. split. tauto. apply H. tauto.
Qed.

Definition lista_updateS {A} {AS : Setoid A} {AP : Pointed A} := injF3 (@lista_update A AS AP) _.

Instance listaCons_Proper A (AS : Setoid A) (AP : Pointed A): Proper (equiv ==> equiv) (@listaCons A).
Proof.
  autounfold. intros. simpl. generalize H. clear H. apply list_ind_2 with (l1:=x ) (l2:=y ).
  simpl. auto.
  intros. inversion H0.
  intros. inversion H0.
  intros. inversion H0. simpl. tauto.
Qed.

Definition listaConsS {A} {AS : Setoid A} {AP :Pointed A}:= injF  (@listaCons A) _.

Fixpoint lista_truncate0 {A} {AS : Setoid A} {AP : Pointed A} n   (l : list A) :=
  match n, l with
    | 0, _ => []
    | S n', [] => []
    | S n', a' :: l' => a' :: lista_truncate0 n' l'
  end
.

Definition lista_truncate {A} {AS : Setoid A} {AP : Pointed A} n (la : lista A) :=
  match la with
    | listaCons _  l => listaCons _  (lista_truncate0 n l)
  end
.

Instance lista_truncate_Proper A (AS : Setoid A) (AP : Pointed A) : Proper (equiv ==> equiv ==> equiv) (@lista_truncate A AS AP).
Proof.
  autounfold. intros. rewrite H. clear x H. destruct x0, y0. generalize y H0. clear y H0. apply list_ind_2 with (l1:=l) (l2:=l0).
  intros. simpl in H0. induction y.
  simpl. tauto.
  simpl. tauto. 
  intros. destruct y.
  simpl in *.  auto.
  simpl in *. split. tauto.  specialize (H y). destruct y. simpl. auto.   apply H. tauto. 
  intros. destruct y.
  simpl in *. auto. 
  simpl in *. split. tauto.  specialize (H y). destruct y. simpl. auto . apply H. tauto. 
  intros. destruct y.
  simpl in *. auto. 
  simpl in *. split. tauto. apply H. tauto.
Qed.

Definition lista_truncateS {A} {AS : Setoid A} {AP : Pointed A} := injF2 (@lista_truncate A AS AP) _.


Lemma lista_truncate_lista_update  :
  forall {A} {AS : Setoid A}{AP :Pointed A} n (a0:A )(n0:nat) (l1 l2:lista A),
    lista_truncate n  l1 == lista_truncate n  l2 ->
    lista_truncate n  (lista_updateS @ n0 @ l1 @ a0) == lista_truncate n  (lista_updateS @ n0 @ l2 @ a0).
Proof.
  destruct l1, l2. generalize n n0. clear n n0. apply list_ind_2 with (l1:=l) (l2:=l0).
  intros. reflexivity.
  intros. destruct n.
  simpl. auto.
  destruct H0. destruct n0. 
  simpl. split. reflexivity.  destruct n. simpl. auto. simpl.  destruct b. auto. auto. 
  simpl. split. symmetry. auto. apply H. simpl. destruct n.  simpl. auto. destruct b. auto. auto. 
  intros. destruct n.
  simpl. auto.
  destruct H0. destruct n0.
  simpl.  split. reflexivity.  destruct n. simpl. auto. simpl.  destruct b. auto. auto. 
  simpl. split. auto. apply H. destruct n.  simpl. auto. destruct b. reflexivity.
  simpl. destruct H1.  auto . 
  intros. destruct n.
  simpl. auto.
  destruct H0. destruct n0.
  simpl. split. reflexivity. auto.
  simpl. split. auto. apply H. auto.
Qed.

Class PointedFunction2 {A B C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C} {AP :Pointed A} {BP :Pointed B} {CP : Pointed C} (f : AS ~> BS ~~> CS) :=
  {
    pointed2 : f @ point @ point == point
  }
.

Fixpoint lista_zipWith0_right {A : Type} {AS : Setoid A} {AP : Pointed A} {B : Type} {BS : Setoid B} {BP : Pointed B} (f : AS ~> BS ~~> AS) {pointed: PointedFunction2 f} (lb : list B) :=
  match lb with
    | [] => []
    | b' :: lb' => (f @ point @ b') :: lista_zipWith0_right f lb'
  end
.

Fixpoint lista_zipWith0 {A : Type} {AS : Setoid A} {AP : Pointed A} {B : Type} {BS : Setoid B} {BP : Pointed B} (f : AS ~> BS ~~> AS) {pointed : PointedFunction2 f} (la : list A)  (lb : list B) :=
  match la, lb with
    | [] , _ => lista_zipWith0_right f lb
    | a' :: la', [] => (f @ a' @ point) :: lista_zipWith0 f la' []
    | a' :: la', b' :: lb' => (f @ a' @ b') :: lista_zipWith0 f la' lb'
  end
.
Definition lista_zipWith {A : Type} {AS : Setoid A} {AP : Pointed A} {B : Type} {BS : Setoid B} {BP : Pointed B} (f : AS ~> BS ~~> AS) {pointed : PointedFunction2 f} (la : lista A) (lb : lista B) :=
  match la, lb with
    | listaCons _ la' , listaCons _ lb' => listaCons _ (lista_zipWith0 f  la' lb')
  end
.


Instance lista_zipWith_Proper {A : Type} {AS : Setoid A} {AP :Pointed A} {B : Type} {BS : Setoid B}{BP : Pointed B}  (f : AS ~> BS ~~> AS) {pointed : PointedFunction2 f}  : Proper ( equiv ==> equiv ==> equiv) (@lista_zipWith A _ _ B _ _ f pointed).
Proof.
  autounfold. intros. destruct x,y,x0,y0. generalize  H  H0. clear H  H0. apply list_ind_4' with (l1:=l) (l2:=l0) (l3:=l1) (l4:=l2).
  
  - auto.
  - intros. simpl in *.  destruct H1. split.
    + rewrite H1.  rewrite pointed2. reflexivity.
    + auto.
  - intros. simpl in *.  destruct H1. split.
    + rewrite H1.  rewrite pointed2. reflexivity.
    + auto.
  - intros. simpl in *. destruct H1. split.
    + rewrite H1.  reflexivity. 
    + auto.
  - intros. simpl in *. destruct H0. split.
    + rewrite H0.  rewrite pointed2. reflexivity. 
    + auto.
  - intros. simpl in *. destruct H0, H1. split.
    + rewrite H0, H1.  rewrite pointed2. reflexivity. 
    + auto.
  - intros. simpl in *. destruct H0, H1. split.
    + rewrite H0, H1.  reflexivity. 
    + auto.
  - intros. simpl in *. destruct H0, H1. split.
    + rewrite H0, H1.  reflexivity. 
    + auto.
  - intros. simpl in *. destruct H0. split.
    + rewrite H0.  rewrite pointed2. reflexivity. 
    + auto.
  - intros. simpl in *.  destruct H0, H1. split.
    + rewrite H0, H1.  reflexivity. 
    + auto.
  - intros. simpl in *.  destruct H0, H1. split.
    + rewrite H0, H1.  rewrite pointed2. reflexivity.
    + auto.
  - intros. simpl in *. destruct H0, H1. split.
    + rewrite H0, H1.  reflexivity. 
    + auto.
  - intros. simpl in *. destruct H0. split.
    + rewrite H0.  reflexivity. 
    + auto.
  - intros. simpl in *. destruct H0, H1. split.
    + rewrite H0, H1.  reflexivity. 
    + auto.
  - intros. simpl in *. destruct H0, H1. split.
    + rewrite H0, H1.  reflexivity. 
    + auto.
  - intros. simpl in *. destruct H0, H1. split.
    + rewrite H0, H1.  reflexivity. 
    + auto.
Qed.


Definition lista_zipWithS {A : Type} {AS : Setoid A} {AP : Pointed A} {B : Type} {BS : Setoid B} {BP : Pointed B} f {poi} := injF2 (@lista_zipWith A _ _ B _ _ f poi) _.


Class PointedFunction {A B } {AS : Setoid A} {BS : Setoid B}  {AP :Pointed A} {BP :Pointed B}  (f : AS ~> BS) :=
  {
    pointed : f @ point  == point
  }
.

Definition lista_map  {A : Type} {AS : Setoid A} {AP : Pointed A}{B : Type} {BS : Setoid B} {BP : Pointed B}(f : AS ~> BS) (poi : PointedFunction f) (la : lista A) :=
  match la with
    | listaCons _ la' => listaCons _ (mapS @ f @ la')
  end
.

Instance lista_map_Proper {A : Type} {AS : Setoid A} AP {B : Type} {BS : Setoid B} BP f poi : Proper (equiv ==> equiv) (@lista_map A _ AP B _ BP f poi) .
Proof.
  autounfold. intros. destruct x,y. unfold lista_map.   generalize H . clear H . apply list_ind_2 with (l1:=l) (l2:=l0).
  - intros. destruct H. rewritesr.
  - intros. destruct H0. split. rewrite H0. apply pointed.  simpl in H. auto. 
  - intros. destruct H0. split. rewrite H0. apply pointed. simpl in H. auto. 
  - intros. destruct H0. split. rewritesr. simpl in H. auto. 
Qed.

Definition lista_mapS  {A : Type} {AS : Setoid A}{AP}{B : Type} {BS : Setoid B}{BP} f {poi}:= injF (@lista_map A AS AP B BS BP f poi) _.

Definition lista_nth {A : Type} {AS : Setoid A}{AP : Pointed A}  n (l : lista A) :=
  match l with
    | listaCons _ l' => nth n l' point
  end
.
Instance lista_nth_Proper {A : Type} {AS : Setoid A} AP : Proper (equiv ==> equiv ==> equiv) (@lista_nth A AS AP).
Proof.
  autounfold. intros. destruct x0, y0. simpl. rewrite H. clear x H. generalize y H0. clear y H0. apply list_ind_2 with (l1:=l) (l2:=l0).
  - simpl. destruct y. reflexivity. reflexivity.
  - intros.  destruct H0.  simpl. destruct y. rewritesr. rewrite <- H. simpl. destruct y. reflexivity. reflexivity. simpl. auto.
  - intros.  destruct H0. simpl. destruct y. rewritesr. rewrite H. simpl. destruct y. reflexivity. reflexivity. simpl. auto.
  - intros.  destruct H0. simpl. destruct y. rewritesr. apply H. simpl.  auto.
Qed.

Definition lista_nthS {A : Type} {AS : Setoid A} {AP} := injF2 (@lista_nth A AS AP) _.

Fixpoint list_findn {A : Type} {AS : Setoid A} {AP : Pointed A} (p : AS ~> boolS) (l : list A)  (n : nat) : maybe nat :=
  match l with
    | [] => if p @ point then Some n else None
    | a' :: l' => if p @ a' then Some n else list_findn p l' (S n)
  end
.

Definition lista_find {A : Type} {AS : Setoid A} {AP : Pointed A} (p : AS ~> boolS) (l : lista A) : maybe nat :=
  match l with
    | listaCons _ l' => list_findn p l' 0
  end
.

Instance lista_find_Proper {A : Type} {AS : Setoid A} AP: Proper (equiv ==> equiv ==> equiv ) (@lista_find A AS AP).
Proof.
  autounfold. intros. destruct x0, y0.  unfold lista_find. generalize 0 H0. clear H0. apply list_ind_2 with (l1:=l) (l2:=l0).
  - intros. destruct H0.  match goal with
      | |- ?a == ?b => simpl a; simpl b
    end. matchequiv.  inversion H0. inversion H0. 
  - intros. destruct H1 as [? ?].
    match goal with
      | |- ?a == ?b => simpl a; simpl b
    end. rewrite H , H1. assert (y @ point = true \/ y @ point = false). destruct (y @ point). tauto. tauto. destruct H3. rewrite H3. reflexivity.  rewrite H3. rewrite <- H0. simpl. rewrite <- H in H3. rewrite H3. auto. simpl.   auto.
  - intros. destruct H1 as [? ?].
    match goal with
      | |- ?a == ?b => simpl a; simpl b
    end. rewrite H , H1. assert (y @ point = true \/ y @ point = false). destruct (y @ point). tauto. tauto. destruct H3. rewrite H3. reflexivity.  rewrite H3. rewrite H0. simpl. rewrite H3. reflexivity.   simpl.   auto.
  - intros. destruct H1 as [? ?].
    match goal with
      | |- ?a == ?b => simpl a; simpl b
    end. rewrite H , H1. assert (y @ c = true \/ y @ c = false). destruct (y @ c). tauto. tauto. destruct H3. rewrite H3. reflexivity.  rewrite H3. apply H0. auto. 
Qed.

Definition lista_findS {A} {AS : Setoid A} {AP} :=
  injF2 (@lista_find A AS AP) _.


Fixpoint list_findan {A : Type} {AS : Setoid A} {AP : Pointed A} (d : forall a a' : A, {a==a'} + {~a==a'}) (l : list A)  (n : nat) :  nat :=
  match l with
    | [] =>  n
    | a' :: l' => if d point a' then  n else list_findan d l' (S n)
  end
.

Definition lista_finda {A : Type} {AS : Setoid A} {AP : Pointed A} (d : forall a a' : A, {a==a'} + {~a==a'}) (l : lista A) :  nat :=
  match l with
    | listaCons _ l' => list_findan d l' 0
  end
.

Instance lista_finda_Proper {A : Type} {AS : Setoid A} AP d: Proper (equiv ==> equiv ) (@lista_finda A AS AP d).
Proof.
  autounfold. intros. destruct x, y.  unfold lista_finda. generalize 0 H. clear H. apply list_ind_2 with (l1:=l) (l2:=l0).
  - intros. simpl. auto. 
  - intros. destruct H0 as [? ?].
    simpl. destruct (d point a). reflexivity.  symmetry in H0. tauto.
    
  - intros. destruct H0 as [? ?].
    simpl. destruct (d point a). reflexivity. symmetry in H0. tauto. 
  - intros. destruct H0 as [? ?].
    match goal with
      | |- ?a == ?b => simpl a; simpl b
    end.  destruct (d point a ), (d point c). reflexivity. rewrite <- H0 in n0. tauto. rewrite H0 in n0. tauto. apply H. auto. 
Qed.

Definition lista_findaS {A} {AS : Setoid A} {AP} d :=
  injF (@lista_finda A AS AP d) _.

Definition lista_repeat {A : Type} {AS : Setoid A} {AP : Pointed A} := listaCons A [].

Fixpoint list_filter' {A : Type} {AS : Setoid A} (l : list (maybe A)) : list A :=
  match l with
    | [] => []
    | a' :: l' => match a' with
                    | Some n => n :: list_filter' l'
                    | None => list_filter' l'
                  end
  end
.

Instance list_filter'_Proper {A : Type} {AS : Setoid A} : Proper (equiv ==> equiv ) (@list_filter' A AS).
Proof.
  autounfold. intros. generalize H. clear H. apply list_ind_2 with (l1:=x) (l2:=y).
  - intros. reflexivity. 
  - intros. inversion H0.
  - intros. inversion H0. 
  - intros. 
    simpl. inversion H0.  destruct a, c.
    + constructor. auto. apply H. auto. 
    + inversion H4.
    + inversion H4.
    + apply H. auto. 
Qed.

Definition lista_filter' {A : Type} {AS : Setoid A} (l : lista (maybe A)) : list A :=
  match l with
    | listaCons _ l' => list_filter' l'
  end
.

Instance lista_filter'_Proper {A : Type} {AS : Setoid A} : Proper (equiv ==> equiv ) (@lista_filter' A AS).
Proof.
  autounfold. intros. destruct x, y.  unfold lista_filter'. generalize H. clear H. apply list_ind_2 with (l1:=l) (l2:=l0).
  - intros. reflexivity. 
  - intros. destruct H0 as [? ?].
    simpl. destruct a.
    + simpl in H0. inversion H0.
    + apply H. apply H1. 
  - intros. destruct H0 as [? ?].
    destruct a.
    + inversion H0.
    + apply H. apply H1.
  - intros. destruct H0 as [? ?].
    simpl. destruct a, c.
    + constructor. auto. apply H. apply H1.
    + inversion H0.
    + inversion H0.
    + apply H. apply H1.
Qed.

Definition lista_filterS' {A} {AS : Setoid A}  :=
  injF (@lista_filter' A AS) _.

Fixpoint list_filter_index {A : Type} {AS : Setoid A} (p : AS ~> boolS) (l : list A) n : list nat :=
  match l with
    | [] => []
    | a' :: l' => if p @ a' then n :: list_filter_index p l' (S n) else list_filter_index p l' (S n)
  end
.

Definition lista_filter_index {A : Type} {AS : Setoid A} {AP : Pointed A} (p : AS ~> boolS) (l : lista A) : list nat :=
  match l with
    | listaCons _ l' => if (p @ point) then [] else list_filter_index p l' 0
  end
.


Instance lista_filter_index_Proper {A : Type} {AS : Setoid A} AP: Proper (equiv ==> equiv ==> equiv ) (@lista_filter_index A AS AP).
Proof.
  autounfold. intros. destruct x0, y0.  unfold lista_filter_index. generalize 0 H0. clear H0. apply list_ind_2 with (l1:=l) (l2:=l0).
  - intros. destruct H0. simpl. matchequiv.  
  - intros. destruct H1 as [? ?].
    match goal with
      | |- ?a == ?b => simpl a; simpl b
    end. rewrite H , <- H1. assert (y @ a = true \/ y @ a = false). destruct (y @ a). tauto. tauto. destruct H3. rewrite H3. reflexivity.  rewrite H3. specialize (H0 (S n)). rewrite <- H1 in H0. rewrite H3 in H0. rewrite <- H in H3. rewrite H3 in H0. rewrite <- H0. simpl. auto.  simpl.   auto.
  - intros. destruct H1 as [? ?].
    match goal with
      | |- ?a == ?b => simpl a; simpl b
    end. rewrite H1.     assert (x @ point = true \/ x @ point = false). destruct (x @ point). tauto. tauto. destruct H3. rewrite H3. rewrite H3 in *.  rewrite H in H3. rewrite H3 in *. reflexivity.  rewrite H3 in *. rewrite  H in H3. rewrite H3 in *. apply H0. auto. 
  - intros. destruct H1 as [? ?].
    match goal with
      | |- ?a == ?b => simpl a; simpl b
    end.  assert (x @ a = true \/ x @ a = false). destruct (x @ a). tauto. tauto. destruct H3. rewrite H, H1 in *. rewrite H3 in *. rewrite <- H in H3. rewrite H3 in *.  destruct (y @ point).
    reflexivity. constructor. reflexivity. apply H0. auto.  rewrite H3. rewrite H, H1 in H3. rewrite H3. rewrite H in *. destruct (y @ point).
    reflexivity. apply H0. auto.
Qed.

Definition lista_filter_indexS {A} {AS : Setoid A} {AP : Pointed A} :=
  injF2 (@lista_filter_index A AS AP) _.



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

Definition lista_filter_index' {A : Type} {AS : Setoid A}   (l : lista (maybe A)) : list (nat * A) :=
  match l with
    | listaCons _  l' => list_filter_index' l' 0
  end
.

Instance lista_filter_index'_Proper {A : Type} {AS : Setoid A}  : Proper (equiv ==> equiv ) (@lista_filter_index' A AS).
Proof.
  autounfold. intros. destruct x, y.  unfold lista_filter_index'. generalize 0 H. clear H. apply list_ind_2 with (l1:=l) (l2:=l0).
  - intros. destruct H. simpl. reflexivity. 
  - intros. destruct H0 as [? ?].   destruct a. inversion H0. simpl. rewrite <- H. reflexivity. simpl.  auto. 
  - intros. destruct H0.   destruct a.  inversion H0. simpl.  rewrite H. simpl. reflexivity.   simpl.   auto.
  - intros. destruct H0.    simpl. matchequiv. constructor. simpl in H2. rewritesr. apply H. auto. apply H. auto.
Qed.

Definition lista_filter_indexS' {A} {AS : Setoid A} :=
  injF (@lista_filter_index' A AS) _.

Lemma lista_equiv_nth :
    forall A (AS : Setoid A) (AP : Pointed A) (l1 l2 : lista A) ,
      (forall ci : nat,
         lista_nth ci l1 ==
         lista_nth ci l2) -> l1 == l2.
Proof.
    intros. destruct l1, l2. generalize H. clear H. apply list_ind_2 with (l1:=l) (l2:=l0).
    intros. reflexivity. 
    intros. split. specialize (H0 0). simpl in H0. symmetry. auto. apply H. intros. specialize (H0 (S ci)). simpl in *. all_cases. 
    intros. split. specialize (H0 0). simpl in H0. auto. apply H. intros. specialize (H0 (S ci)). simpl in *. all_cases. 
    intros. split. specialize (H0 0). simpl in H0. auto. apply H. intros. specialize (H0 (S ci)). simpl in *. auto. 
Qed.

Lemma equiv_nth :
    forall A (AS : Setoid A) (a : A) l1 a2 l2,
      (forall ci : nat,
         nth ci l1 a ==
         nth ci l2 a2) -> a == a2.
Proof.
    intros.  generalize H. clear H. apply list_ind_2 with (l1:=l1) (l2:=l2).
    intros. specialize (H 0). auto.
    intros. apply H. intros. specialize (H0 (S ci)). simpl in H0. simpl. all_cases.
    intros. apply H. intros. specialize (H0 (S ci)). simpl in H0. simpl. all_cases.
    intros. apply H. intros. specialize (H0 (S ci)). simpl in H0. auto.
Qed.
  
  Lemma listAll_nth :
    forall A (AS : Setoid A) (AP : Pointed A) l,
      (forall ci : nat,
         nth ci l point  == point) -> list_all l.
  Proof.
    intros.  generalize H. clear H. induction l. 
    intros. simpl. auto. 
    intros. split. specialize (H 0). simpl in H. auto. apply IHl. intros. specialize (H (S ci)). simpl in H. auto.
  Qed.

  Lemma equiv_lista :
    forall A (AS : Setoid A) (AP : Pointed A)  l1  l2,
      (forall ci : nat,
         nth ci l1 point ==
         nth ci l2 point) ->
      lista_equiv0 l1 l2.
  Proof.
    intros. generalize H. clear H. apply list_ind_2 with (l1:=l1) (l2:=l2).
    intros. specialize (H 0). simpl in H. simpl. auto.
    intros. split. specialize (H0 0).  simpl in H0. symmetry. auto. apply listAll_nth. intros.  specialize (H0 (S ci)).   simpl in H0. symmetry. auto. 
    intros. split. specialize (H0 0).  simpl in H0. auto. apply H.  intros. specialize (H0 (S ci)). simpl in H0.  generalize H0. simpl.  all_cases.
    intros. split. specialize (H0 0).  simpl in H0. auto. apply H.  intros. specialize (H0 (S ci)). simpl in H0.  auto.
  Qed.

  Definition listOfLista {A} {AS : Setoid A} (l : lista A) :=
    match l with
      | listaCons _ l => l
    end.
  
  Lemma eq_lista_nth_lista_truncate_lt_lista_nth :
    forall A (AS : Setoid A) (AP : Pointed A) m n l,
      m < n ->
      lista_nth m (lista_truncate n  l) = lista_nth m l.
  Proof.
    intros. destruct l. generalize m n H. clear m n H. induction l.
    - double induction m n.
      + intros. inversion H.
      + intros. simpl. auto. 
      + intros. inversion H0.
      + intros. simpl. destruct n1, n.
        * inversion H1. inversion H3.
        * simpl. auto.
        * inversion H1. inversion H3.
        * auto. 
    - intros. destruct m, n.
      + inversion H.
      + simpl. auto.
      + inversion H.
      + simpl. apply IHl. apply lt_S_n. auto.
  Qed.
  
  Lemma lista_truncate_nil :
    forall n, lista_truncate0 n nil = nil.
  Proof.
    destruct n. auto. auto.
  Qed.

   Lemma lista_equiv_nil :
    forall A (AS : Setoid A) (AP : Pointed A) (l : list A), list_all l -> lista_equiv0 l [].
  Proof.
    induction l. auto. intros. destruct H. split. auto. auto.
  Qed.
  
    
  Lemma equiv_nth_equiv_lista_truncate :
    forall A (AS : Setoid A) n  l1 l2,
      (forall ci : nat, ci < n ->
         lista_nth ci l1 ==
         lista_nth ci l2) ->
      lista_truncate n l1 == lista_truncate n l2.
  Proof.
    intros. destruct l1, l2. generalize l l0 H. clear l l0 H. induction n.
    - intros. simpl. auto.
    - intros. generalize H. clear H.  apply list_ind_2 with (l1:=l) (l2:=l0).
      +  intros. reflexivity. 
      + intros. split.
        * simpl.  specialize (H0 0). simpl in H0. symmetry. apply H0. apply lt_O_Sn.
        * specialize IHn with (l:=nil) (l0:=b).  simpl in IHn. rewrite lista_truncate_nil in IHn. simpl in IHn. apply IHn. intros.  specialize (H0 (S ci)). simpl in H0. rewrite <- H0.  all_cases.  auto using lt_n_S.
      + intros. split.
        * simpl.  specialize (H0 0). simpl in H0. apply H0. apply lt_O_Sn.
        * specialize IHn with (l:=b) (l0:=nil).  simpl in IHn. rewrite lista_truncate_nil in IHn. simpl in IHn.  apply IHn. intros.  specialize (H0 (S ci)). simpl in H0. rewrite  H0.  all_cases.  auto using lt_n_S.
      + intros. split.
        * simpl.  specialize (H0 0). simpl in H0. apply H0. apply lt_O_Sn.
        * specialize IHn with (l:=b) (l0:=d).   simpl in IHn. apply IHn. intros.  specialize (H0 (S ci)). simpl in H0. rewrite  H0.  auto.  auto using lt_n_S.
  Qed.

  Lemma equiv_lista_truncate_equiv_nth :
    forall A (AS : Setoid A) n l1 l2,
      lista_truncate n  l1 == lista_truncate n l2 ->
      (forall ci : nat, ci < n ->
         lista_nth ci l1 ==
         lista_nth ci l2).
  Proof.
    intros.  destruct l1, l2. generalize H0 H. clear H0 H.  apply nat_list_ind_4 with (l1:=ci) (l2:=n) (l3:=l) (l4:=l0).
    - intros. inversion H0.
    - intros. inversion H0.
    - intros. inversion H0.
    - intros. inversion H0.
    - intros. simpl.  destruct H1. auto.
    - intros. simpl.  destruct H1. auto.
    - intros. simpl.  destruct H1. auto.
    - intros. simpl.  destruct H1. auto.
    - intros. inversion H0.
    - intros. inversion H0.
    - intros. inversion H0.
    - intros. inversion H0.
    - intros. simpl. auto. 
    - intros. simpl. destruct z.
      + apply H. apply lt_S_n. auto. destruct H1. simpl. rewrite lista_truncate_nil. auto. 
      + apply H. apply lt_S_n. auto. destruct H1. simpl. rewrite lista_truncate_nil. auto.
    - intros. simpl. destruct z.
      + apply H. apply lt_S_n. auto. destruct H1. simpl.  rewrite lista_truncate_nil. auto. 
      + apply H. apply lt_S_n. auto. destruct H1. simpl. rewrite lista_truncate_nil. auto.
    - intros. simpl. destruct z.
      + apply H. apply lt_S_n. auto. destruct H1. auto. 
      + apply H. apply lt_S_n. auto. destruct H1. auto.
  Qed.

  Lemma lista_nth_ge_length :
    forall A(AS : Setoid A) (AP : Pointed A) n l,
      length l <= n ->
      lista_nth n (listaCons _ l) = point.
  Proof.
    intros. generalize dependent n. induction l.
    intros. destruct n.  auto. auto.
    intros. destruct n. simpl.  inversion H. simpl. apply IHl. auto using le_S_n.
  Qed.
  Lemma length_map : forall A B (l : list A) (f : A -> B), length (map f l) = length l.
  Proof.
    induction l.
    intros. auto. intros. simpl. f_equal. auto.
  Qed.


Lemma lista_truncate_equiv_equiv : forall A (AS : Setoid A) (AP :Pointed A) l1 l2 n,  l1 == l2 -> lista_truncate n l1 == lista_truncate n l2.
Proof.
  intros. generalize n H. clear n H . destruct l1, l2. apply list_ind_2 with (l1:=l) (l2:=l0).
  - simpl. intros. induction n.
    + simpl. auto. 
    + simpl. tauto.
  - intros. destruct H0.   induction n.
    + simpl. auto. 
    + simpl. split. auto. specialize (H n H1). simpl in H. destruct n. apply H. auto. 
  - intros. destruct H0.  induction n.
    + simpl. auto.  
    + simpl. split. auto. specialize (H n H1). simpl in H. destruct n. apply H. auto. 
  - intros. destruct H0.  induction n.
    + simpl. auto.  
    + simpl. split. auto. specialize (H n H1). simpl in H. destruct n. apply H. auto. 
Qed.


Lemma truncate_idempotent:
  forall A (AS : Setoid A) (AP : Pointed A) n  (l : lista A),
    lista_truncate n  (lista_truncate n  l) == lista_truncate n  l.
Proof.
  intros. destruct l. apply nat_list_ind_2 with (l1:=n) (l2:=l).
  - reflexivity.
  - intros. simpl. auto.
  -    intros. simpl. auto. 
  -    intros. split. reflexivity    . auto.
Qed.

Lemma lista_nth_lista_update: forall
  (A : Type)
  (AS : Setoid A)
  (AP : Pointed A)
  n 
  (a : A)
  (l : lista A), lista_nth n (lista_update n l a)  = a.
Proof.
  intros. destruct l. simpl. apply nat_list_ind_2 with (l1:=n) (l2:=l).
  - simpl. reflexivity.
  - intros. simpl in *. reflexivity.
  - intros. simpl in *. auto. 
  - intros. simpl in *. auto. 
Qed.

Lemma lista_nth_lista_update_equiv: forall
  (A : Type)
  (AS : Setoid A)
  (AP : Pointed A)
  n 
  (a : A)
  (l : lista A), lista_nth n (lista_update n l a)  == a.
Proof.
  intros. apply eq_equiv. apply lista_nth_lista_update.
Qed.

Lemma lista_update_lista_nth: forall
  (A : Type)
  (AS : Setoid A)
  (AP : Pointed A)
  n 
  (l : lista A),  (lista_update n l (lista_nth n l))  == l.
Proof.
  intros.  destruct l.  apply nat_list_ind_2 with (l1:=n) (l2:=l).
  - simpl. split; [reflexivity  | reflexivity]. 
  - intros.  split. reflexivity. assert (listaCons _ b == listaCons _ b). reflexivity.   auto. 
  - intros. simpl in *. split ; [reflexivity | ]. destruct b.
      * simpl in *. auto. 
      * simpl in *. auto. 
  - intros. simpl in *. split ; [reflexivity | auto].
  
Qed.

Lemma lista_update_lista_update: forall
  (A : Type)
  (AS : Setoid A)
  (AP : Pointed A)
  n
  a c
  (l : lista A),  (lista_update n (lista_update n l a) c )  == lista_update n l c .
Proof.
  intros. destruct l. simpl. apply nat_list_ind_2 with (l1:=n) (l2:=l).
    - simpl. split; [reflexivity | reflexivity]. 
    - intros. simpl in *. split; [reflexivity |]. destruct b.
      * simpl in *. tauto. 
      * simpl in *. split ; [reflexivity | tauto]. 
    - intros. simpl in *. split ; [reflexivity | auto].
    - intros. simpl in *. split ; [reflexivity | auto].
  
Qed.

Lemma lista_nth_lista_update_diff_index: forall
  (A : Type)
  (AS : Setoid A)
  (AP : Pointed A)
  n n' a
  (l : lista A), 
  n <> n' ->lista_nth n' (lista_update n l a) = lista_nth n' l.
Proof.
  intros.  destruct l. generalize H a. clear H. apply nat_list_ind_4 with (l1:=n) (l2:=n')(l3:=l).
  - intros. destruct H.  auto.
  - intros. destruct H0.  auto.
  - intros. destruct H0. auto. 
  - intros. destruct H0. auto. 
  - intros. simpl. all_cases. 
  - intros. simpl. all_cases.
  - intros. simpl. auto. 
  - intros. simpl. auto.
  - intros. simpl. auto. 
  - intros. simpl. auto.
  - intros. simpl. auto.
  - intros. simpl. auto.
  - intros. simpl in *. destruct b. apply H. auto. apply H. auto. 
  - intros. simpl in *. destruct b. apply H. auto. apply H. auto.
  - intros. simpl in *. apply H. auto.
  - intros. simpl in *. apply H. auto.
  - exact [].
Qed.
Lemma lista_update_lista_update_diff_index: forall
  (A : Type)
  (AS : Setoid A)
  (AP : Pointed A)
  n n' a a'
  (l : lista A), 
  n <> n' -> lista_update n' (lista_update n l a) a' = lista_update n (lista_update n' l a') a.
Proof.
  intros.  destruct l. generalize H a a'. clear H. apply nat_list_ind_4 with (l1:=n) (l2:=n')(l3:=l).
  - intros. destruct H.  auto.
  - intros. destruct H0.  auto.
  - intros. destruct H0. auto. 
  - intros. destruct H0. auto. 
  - intros. simpl. auto. 
  - intros. simpl. auto. 
  - intros. simpl. auto. 
  - intros. simpl. auto.
  - intros. simpl. auto. 
  - intros. simpl. auto.
  - intros. simpl. auto.
  - intros. simpl. auto.
  - intros. simpl in *. assert (z<>b); [auto|]. specialize (H H1 a0 a'0). inversion H. congruence. 
  - intros. simpl in *. assert (z<>b); [auto|]. specialize (H H1 a0 a'0). inversion H. congruence.
  - intros. simpl in *. assert (z<>b); [auto|]. specialize (H H1 a0 a'0). inversion H. congruence.
  - intros. simpl in *. assert (z<>b); [auto|]. specialize (H H1 a0 a'0). inversion H. congruence.
  - exact [].
Qed.

Lemma list_update_list_update_diff_index: forall
  (A : Type)
  (AS : Setoid A)
  n n' a a'
  (l : list A), 
  n <> n' -> list_update' n' (list_update' n l a) a' = list_update' n (list_update' n' l a') a.
Proof.
  intros.  generalize H a a'. clear H. apply nat_list_ind_4 with (l1:=n) (l2:=n')(l3:=l).
  - intros. destruct H.  auto.
  - intros. destruct H0.  auto.
  - intros. destruct H0. auto. 
  - intros. destruct H0. auto. 
  - intros. simpl. auto. 
  - intros. simpl. auto. 
  - intros. simpl. auto. 
  - intros. simpl. auto.
  - intros. simpl. auto. 
  - intros. simpl. auto.
  - intros. simpl. auto.
  - intros. simpl. auto.
  - intros. simpl in *. assert (z<>b); [auto|]. specialize (H H1 a0 a'0). inversion H. congruence. 
  - intros. simpl in *. assert (z<>b); [auto|]. specialize (H H1 a0 a'0). inversion H. congruence.
  - intros. simpl in *. assert (z<>b); [auto|]. specialize (H H1 a0 a'0). inversion H. congruence.
  - intros. simpl in *. assert (z<>b); [auto|]. specialize (H H1 a0 a'0). inversion H. congruence.
  - exact [].
Qed.

Require Import Coq.Arith.Le.

  Lemma list_findan_ge : forall A (AS : Setoid A )(AP : Pointed A) (l: list A) n
                            (equiv_dec: forall a a' : A, {a == a'} + {~ a == a'}),
                            list_findan equiv_dec l n >= n.
  Proof.
    intros. generalize n. induction l.
    simpl. apply le_n.
    simpl. destruct (equiv_dec point a).
    apply le_n.
    intros. apply le_trans with (m:=S n1).
    apply Nat.le_le_succ_r. apply le_n.
    apply IHl.
  Qed.
  Open Scope nat_scope.
  Lemma list_findan_plus : forall A (AS : Setoid A )(AP : Pointed A) (l: list A) m n
                            (equiv_dec: forall a a' : A, {a == a'} + {~ a == a'}),
                            list_findan equiv_dec l (m + n) = list_findan equiv_dec l m + n.
  Proof.
    intros. generalize m n. induction l.
    intros. simpl. reflexivity .
    intros. simpl. destruct (equiv_dec point a).
    auto.
    apply (IHl (S m0) n0).
  Qed.

  Lemma list_filter_index_plus : forall A (AS : Setoid A )(AP : Pointed A) (l: list A) q m n
                            ,
                            list_filter_index q l (m + n) = map (flip plus n) (list_filter_index q l m ).
  Proof.
    intros. generalize m n. induction l.
    intros. simpl. reflexivity .
    intros. simpl. destruct (q @ a).
    rewrite map_cons. f_equal. rewrite <- plus_Sn_m. apply IHl.
    rewrite <- plus_Sn_m. apply IHl.
  Qed.

  Lemma list_filter_index_plus' : forall A (AS : Setoid A) (l: list (maybe A))  m n
                            ,
                            list_filter_index'  l (m + n) = mapS @ (flipS @ plusS @ n *** idS) @ (list_filter_index'  l m ).
  Proof.
    intros. generalize m n. induction l.
    intros. simpl. reflexivity .
    intros. simpl. destruct a.
    rewrite map_cons. f_equal. rewrite <- plus_Sn_m. apply IHl.
    rewrite <- plus_Sn_m. apply IHl.
  Qed.

  Lemma lista_finda_lista_update:
  forall
  (A : Type)
  (AS : Setoid A)
  (AP : Pointed A)equiv_dec
  n  a
  (l : lista A), 
    ~    lista_nth n l == point ->
    ~ a == point -> 
    lista_finda equiv_dec
    (lista_update n l a) =
       lista_finda equiv_dec
                 l.
Proof.
  intros. destruct l. generalize H. clear H. apply nat_list_ind_2 with (l1:=n) (l2:=l).
  - intros. simpl in *. destruct H. reflexivity.
  - intros. simpl in *. destruct (equiv_dec point a), (equiv_dec point a0).  auto. symmetry in e.  tauto.  symmetry in e. tauto. auto.
  - intros. simpl in *. destruct H1. reflexivity.
  - intros. simpl in *. destruct (equiv_dec point c). auto. rewrite (list_findan_plus _ _ _ (lista_update0 b d a) 0 1 _). rewrite (list_findan_plus _ _ _ d 0 1 _). f_equal. auto.
Qed.

Lemma lista_update_lista_finda:

  forall
  (A : Type)
  (AS : Setoid A)
  (AP : Pointed A)equiv_dec
  (l : lista A), 
    (lista_update (lista_finda equiv_dec l) l point) ==
                 l.
Proof.
  intros. destruct l. induction l. 
  - intros. simpl in *. split.  reflexivity. auto.
    
  - intros. simpl in *.  destruct (equiv_dec point a).   simpl. split.  auto. fold (lista_equiv (listaCons _ l) (listaCons _ l)). reflexivity. rewrite (list_findan_plus _ _ _ l 0 1). rewrite <- plus_n_Sm.    simpl. split. reflexivity. rewrite <- plus_n_O.  auto. 
Qed.


  Existing Instance list_Foldable.
  Existing Instance listFunctor.
Section And_Monoid.
  Existing Instance and_Monoid.
    Lemma filterTrue :
      forall A (AS : Setoid A)
             (p : maybeS AS ~> iff_setoid)
             (q : maybeS AS ~> boolS)
             (a : lista (maybe A)),
        (forall b : maybe A, q @ b == true -> p @ b) ->
        fold @ (mapS @ (p ∘ flipS @ lista_nthS @ a) @ (lista_filter_indexS @ q @ a)) == True.
    Proof.
      intros. destruct a. induction l.
      simpl.  destruct_bool (q @ None). tauto. tauto.
      split. auto. intros. simpl in *. destruct_bool (q @ None). auto. destruct_bool (q @ a).
      - split.
        + apply H. auto.
        + rewrite (list_filter_index_plus _ _ _ _ _ 0 1). rewrite map_map. unfold flip.  generalize IHl. clear IHl. induction l.
          * simpl. auto.
          * intros. simpl. destruct_bool (q @ a0).
            {
              split.
              {
                tauto.
              }
              {
                clear IHl. generalize IHl0. clear IHl0. 
                induction (list_filter_index q l 1).
                {
                  auto.
                }
                {
                  intros. destruct IHl1. destruct H5. auto. destruct H6. split.
                  {
                    rewrite <- (plus_n_Sm a1 0). rewrite <- plus_n_O. auto.
                  }
                  {
                    apply IHl0. split.  auto. intro. auto.
                  }
                }
              }
            }
            {
                clear IHl. generalize IHl0. clear IHl0. 
                induction (list_filter_index q l 1).
                {
                  auto.
                }
                {
                  intros. destruct IHl1. destruct H5. auto. split.
                  {
                    rewrite <- (plus_n_Sm a1 0). rewrite <- plus_n_O. auto.
                  }
                  {
                    apply IHl0. split.  auto. intro. auto.
                  }
                }
              }
      -  rewrite (list_filter_index_plus _ _ _ _ _ 0 1). rewrite map_map. unfold flip.  generalize IHl. clear IHl. induction l.
          * simpl. auto.
          * intros. simpl. destruct_bool (q @ a0).
            {
              split.
              {
                tauto.
              }
              {
                clear IHl. generalize IHl0. clear IHl0. 
                induction (list_filter_index q l 1).
                {
                  auto.
                }
                {
                  intros. destruct IHl1. destruct H5. auto. destruct H6. split.
                  {
                    rewrite <- (plus_n_Sm a1 0). rewrite <- plus_n_O. auto.
                  }
                  {
                    apply IHl0. split.  auto. intro. auto.
                  }
                }
              }
            }
            {
                clear IHl. generalize IHl0. clear IHl0. 
                induction (list_filter_index q l 1).
                {
                  auto.
                }
                {
                  intros. destruct IHl1. destruct H5. auto. split.
                  {
                    rewrite <- (plus_n_Sm a1 0). rewrite <- plus_n_O. auto.
                  }
                  {
                    apply IHl0. split.  auto. intro. auto.
                  }
                }
            }
    Qed.

    Lemma filterTrue' :
      forall A (AS : Setoid A)
             (a : lista (maybe A)),
        fold @ (mapS @ (uncurryS @ equivS ∘ (flipS @ lista_nthS @ a *** SomeS)) @ (lista_filter_indexS' @ a)) == True.
    Proof.
      intros. destruct a. induction l.
      simpl. reflexivity.
      split. auto. intros. simpl in *. destruct a.
      - simpl. split.
        + reflexivity.
        + rewrite (list_filter_index_plus' _ _ _ 0 1). unfold mapS. normalize. rewrite map_map. unfold flipS, flip.  normalize. generalize IHl. clear IHl. induction l.
          * simpl. auto.
          * intros. simpl in *. destruct a0.
            {
              split.
              {
                simpl. reflexivity. 
              }
              {
                clear IHl. generalize IHl0. clear IHl0. 
                induction (list_filter_index' l 1).
                {
                  auto.
                }
                {
                  intros. destruct IHl1. destruct H1. auto. destruct H2. split.
                  {
                    destruct a1. rewrite <- (plus_n_Sm n 0). rewrite <- plus_n_O. auto.
                  }
                  {
                    apply IHl0. split.  auto. intro. split. reflexivity. auto.
                  }
                }
              }
            }
            {
                clear IHl. generalize IHl0. clear IHl0. 
                induction (list_filter_index' l 1).
                {
                  auto.
                }
                {
                  intros. destruct IHl1. destruct H1. auto. split.
                  {
                    destruct a0. rewrite <- (plus_n_Sm n 0). rewrite <- plus_n_O. auto.
                  }
                  {
                    apply IHl0. split.  auto. intro. auto.
                  }
                }
              }
      -  rewrite (list_filter_index_plus' _ _ _ 0 1). unfold mapS. normalize. rewrite map_map. unfold flipS, flip.  normalize. generalize IHl. clear IHl. induction l.
          * simpl. auto.
          * intros. simpl in *. destruct a.
            {
              split.
              {
                simpl. reflexivity. 
              }
              {
                clear IHl. generalize IHl0. clear IHl0. 
                induction (list_filter_index' l 1).
                {
                  auto.
                }
                {
                  intros. destruct IHl1. destruct H1. auto. destruct H2. split.
                  {
                    destruct a0. rewrite <- (plus_n_Sm n 0). rewrite <- plus_n_O. auto.
                  }
                  {
                    apply IHl0. split.  auto. intro. split. reflexivity. auto.
                  }
                }
              }
            }
            {
                clear IHl. generalize IHl0. clear IHl0. 
                induction (list_filter_index' l 1).
                {
                  auto.
                }
                {
                  intros. destruct IHl1. destruct H1. auto. split.
                  {
                    destruct a. rewrite <- (plus_n_Sm n 0). rewrite <- plus_n_O. auto.
                  }
                  {
                    apply IHl0. split.  auto. intro. auto.
                  }
                }
            }
    Qed.
End And_Monoid.

    Definition SS : natS ~> natS := injF S _.
Section Or_Monoid.
  Existing Instance or_Monoid.
    Lemma filterTrue_one :
      forall A (AS : Setoid A) (AP : Pointed A)
             (p : natS ~> iff_setoid)
             (q : AS ~> boolS)
             (a : lista A),
        q @ point = false ->
        (exists b : nat, q @ (lista_nthS @ b @ a) == true /\ p @ b) ->
        fold @ (mapS @ p @ (lista_filter_indexS @ q @ a)) == True.
    Proof.
      intros. destruct a. generalize dependent p. induction l.
      intros. simpl. destruct H0. simpl in H0. destruct x. destruct H0. rewrite H in H0. inversion H0.  destruct H0. rewrite H in H0. inversion H0.
      split. auto. intros. simpl in *. rewrite H in *. destruct H0.  destruct x.
      - destruct H0. rewrite H0. simpl. left. auto. 
      - destruct (q @ a).
        + simpl. right. rewrite (list_filter_index_plus _ _ _ _ _ 0 1). rewrite map_map. unfold flip. destruct (IHl (p ∘ SS)). exists x.   auto. clear H0 H1 H2. specialize (H3 I). generalize H3. clear H3. induction l.
          * simpl. auto.
          * intros. destruct_bool (q @ a0).
            {
              destruct H3. 
              {
                tauto.
              }
              {
                generalize H1. clear H1. 
                induction (list_filter_index q l 1).
                {
                  auto.
                }
                {
                  intros. destruct H1.  destruct a1. tauto. right. left. simpl. rewrite <- (plus_n_Sm a1 0). rewrite <- plus_n_O. auto. right. right. clear H H0 IHl IHl0 IHl1. induction l0.
                  {
                    simpl in *. auto.
                  }
                  {
                    simpl in *. destruct H1.
                    {
                      left.  rewrite <- plus_n_Sm. rewrite <- plus_n_O.  auto.
                    }
                    {
                      right. auto. 
                    }
                  }
                }
              }
            }
            {
                clear IHl IHl0. generalize H3. clear H3. 
                induction (list_filter_index q l 1).
                {
                  auto.
                }
                {
                  intros. simpl.  destruct H3. destruct a1.  simpl. tauto. simpl.  rewrite <- (plus_n_Sm a1 0). rewrite <- plus_n_O. tauto. right. apply IHl0. auto. 
                }
            }
        + rewrite (list_filter_index_plus _ _ _ _ _ 0 1). rewrite map_map. unfold flip. destruct (IHl (p ∘ SS)). exists x.   auto. clear H0 H1 H2. specialize (H3 I). generalize H3. clear H3. induction l.
          * simpl. auto.
          * intros. destruct_bool (q @ a0).
            {
              destruct H3. 
              {
                tauto.
              }
              {
                generalize H1. clear H1. 
                induction (list_filter_index q l 1).
                {
                  auto.
                }
                {
                  intros. destruct H1.  destruct a1. tauto. right. left. simpl. rewrite <- (plus_n_Sm a1 0). rewrite <- plus_n_O. auto. right. right. clear H H0 IHl IHl0 IHl1. induction l0.
                  {
                    simpl in *. auto.
                  }
                  {
                    simpl in *. destruct H1.
                    {
                      left.  rewrite <- plus_n_Sm. rewrite <- plus_n_O.  auto.
                    }
                    {
                      right. auto. 
                    }
                  }
                }
              }
            }
            {
                clear IHl IHl0. generalize H3. clear H3. 
                induction (list_filter_index q l 1).
                {
                  auto.
                }
                {
                  intros. simpl.  destruct H3. destruct a1.  simpl. tauto. simpl.  rewrite <- (plus_n_Sm a1 0). rewrite <- plus_n_O. tauto. right. apply IHl0. auto. 
                }
            }
    Qed.

    Lemma filterTrue_one' :
      forall A (AS : Setoid A)
             (p : natS ~*~ AS ~> iff_setoid)
             (a : lista (maybe A)),
        (exists (b : nat) c, lista_nthS @ b @ a == Some c /\ p @ (b, c)) ->
        fold @ (mapS @ p @ (lista_filter_indexS' @ a)) == True.
    Proof.
      intros. destruct a. generalize dependent p. induction l.
      intros. simpl. destruct H as [b [c H]]. simpl in H. destruct b. destruct H. inversion H.  destruct H.  inversion H.
      split. auto. intros. simpl in *. clear H0.  destruct H as [b [c H]].  destruct b.
      - destruct H. destruct a.
        + simpl in *. left. assert (p @ (0, a) == p @ (0, c)). evalproper.  split; [reflexivity | auto]. rewrite H1. auto. 
        + simpl in *. tauto. 
      - destruct a.
        + simpl. right. rewrite (list_filter_index_plus' _ _ _ 0 1). unfold mapS. normalize. rewrite map_map. destruct (IHl (p ∘ (SS *** idS))). clear IHl.  exists b.   exists c. auto. clear H H0. specialize (H1 I). generalize H1. clear H1. induction l.
          * simpl. auto.
          * intros. simpl. destruct a0. 
            {
              simpl. destruct H1. 
              {
                left. auto. 
              }
              {
                clear IHl. right. generalize H. clear H. 
                induction (list_filter_index' l 1).
                {
                  auto.
                }
                {
                  intros. destruct H.
                  {
                    destruct a1. simpl.
                    left.  rewrite <- (plus_n_Sm n 0). rewrite <- plus_n_O. destruct n.
                    auto. auto.
                  }
                  {
                    right. auto. 
                  }
                }
              }
            }
            {
              simpl in H1. clear IHl.  generalize H1. clear H1. 
                induction (list_filter_index' l 1).
                {
                  auto.
                }
                {
                  intros. destruct H1.
                  {
                    destruct a0. simpl.
                    left.  rewrite <- (plus_n_Sm n 0). rewrite <- plus_n_O. destruct n.
                    auto. auto.
                  }
                  {
                    right. auto. 
                  }
                }
            }
        + rewrite (list_filter_index_plus' _ _ _ 0 1). unfold mapS. normalize. rewrite map_map. destruct (IHl (p ∘ (SS *** idS))). clear IHl.  exists b.   exists c. auto. clear H H0. specialize (H1 I). generalize H1. clear H1. induction l.
          * simpl. auto.
          * intros. simpl. destruct a. 
            {
              simpl. destruct H1. 
              {
                left. auto. 
              }
              {
                clear IHl. right. generalize H. clear H. 
                induction (list_filter_index' l 1).
                {
                  auto.
                }
                {
                  intros. destruct H.
                  {
                    destruct a0. simpl.
                    left.  rewrite <- (plus_n_Sm n 0). rewrite <- plus_n_O. destruct n.
                    auto. auto.
                  }
                  {
                    right. auto. 
                  }
                }
              }
            }
            {
              simpl in H1. clear IHl.  generalize H1. clear H1. 
                induction (list_filter_index' l 1).
                {
                  auto.
                }
                {
                  intros. destruct H1.
                  {
                    destruct a. simpl.
                    left.  rewrite <- (plus_n_Sm n 0). rewrite <- plus_n_O. destruct n.
                    auto. auto.
                  }
                  {
                    right. auto. 
                  }
                }
            }
    Qed.
    

End Or_Monoid.

    Fixpoint list_filter_index_2 {A}  {AS : Setoid A} (p : AS ~> boolS) 
             (l : list A)  :=
      match l with
        | nil => nil
        | a' :: l' =>
          if p @ a'
          then 0 :: map S (list_filter_index_2  p l')
          else map S (list_filter_index_2 p l')
      end.

    Definition lista_filter_index_2 {A}  {AS : Setoid A} {AP : Pointed A} (p : AS ~> boolS) 
             (l : lista A) :=
      match l with
        | listaCons _ l' => if p @ point then nil else list_filter_index_2 p l'
      end.

    Lemma list_filter_index_eq : forall A (AS : Setoid A)  (p : AS ~> boolS) (l : list A) n,
                                     list_filter_index p l n = map (plus n) (list_filter_index_2 p l).
    Proof.
      intros. generalize n. induction l. 
      simpl. auto.
      intros.       simpl. destruct (p @ a). rewrite map_cons. f_equal.  auto. rewrite map_map. rewrite IHl. clear IHl.  induction ((list_filter_index_2 p l)).    auto. simpl. f_equal. auto. auto. rewrite map_map. rewrite IHl. clear IHl.  induction ((list_filter_index_2 p l)).    auto. simpl. f_equal. auto. auto.
    Qed.
      
    Lemma lista_filter_index_eq : forall A (AS : Setoid A) (AP : Pointed A) (p : AS ~> boolS) (l : lista A),
            lista_filter_index p l  = lista_filter_index_2 p l.
    Proof.
      intros. destruct l. induction l. 
      simpl. reflexivity. 
      simpl. destruct (p @ point).
      auto.
      destruct (p @ a).  f_equal. rewrite list_filter_index_eq.  clear IHl. induction ((list_filter_index_2 p l)).  auto. simpl. f_equal. rewrite list_filter_index_eq.  clear IHl. induction ((list_filter_index_2 p l)).  auto. simpl. f_equal. 
    Qed.


        Fixpoint list_zipWith_not_proper {A B C} (f : A -> B -> C) l1 l2 :=
      match l1, l2 with
        | nil, _ => nil
        | a :: l1', nil => nil
        | a :: l1', b :: l2' => f a b :: list_zipWith_not_proper f l1' l2'
      end
    .    

(*  Fixpoint compact {A} {AS : Setoid A} (l1  : list (maybe A)) :=
    match l1 with
      | nil => nil
      | None :: l2' => compact l2'
      | Some a :: l2' => Some a :: compact l2'
    end.*)
  
  Fixpoint list_merge {A} {AS : Setoid A} (l1  : list (maybe A)) (l2 : list A) :=
    match l1, l2 with
      | nil, _ => map Some l2
      | None :: l1', nil => list_merge l1' nil
      | None :: l1', a :: l2' => Some a :: list_merge l1' l2'                   
      | Some a :: l1', _ => Some a :: list_merge l1' l2
    end
  .

(*  Instance list_merge_Proper A AS : Proper (equiv ==> equiv ==> equiv) (@list_merge A AS).
  Proof.
    autounfold. intros. generalize H x0 y0 H0. clear H x0 y0 H0. apply list_ind_2 with (l1:=x) (l2:=y).
    intros. unfold list_merge.  apply map_Proper. auto. auto.
    intros. inversion H0. 
    intros. inversion H0. 
    intros. inversion H0. unfold list_merge. fold list_merge.      matchequiv. constructor. auto. apply H. auto. auto. matchequiv. auto. inversion H9. constructor. auto. apply H. auto. auto.
  Qed.
  *)

  Definition lista_merge {A} {AS : Setoid A} (l1 : lista (maybe A)) (l2 : list A) :=
    match l1 with
      | listaCons _ l1 => listaCons _ (list_merge l1 l2)
    end
  .

  
  Instance lista_merge_Proper A AS : Proper (equiv ==> equiv ==> equiv) (@lista_merge A AS).
  Proof.
    autounfold. intros. destruct x,y. unfold lista_merge. simpl in H. generalize H x0 y0 H0. clear H x0 y0 H0. apply list_ind_2 with (l1:=l) (l2:=l0).
    -    intros. unfold list_merge.  rewritesr. 
    - intros.  destruct a.
      + inversion H0. inversion H2.
      + rewrite H with (y0:=y0).
        * simpl. clear H H1. generalize b H0. clear b H0. induction y0.
          {
            reflexivity.
          }
          {
            intros. destruct b. reflexivity. destruct m.
            inversion H0. inversion H1. inversion H2.
            simpl. split. reflexivity. apply IHy0. simpl in H0. simpl. tauto.
          }
        * simpl in H0. tauto.
        * auto.
    - intros.  destruct a.
      + inversion H0. inversion H2.
      + rewrite <- H with (x0:=x0).
        * simpl. clear H H1. generalize b H0. clear b H0. induction x0.
          {
            reflexivity.
          }
          {
            intros. destruct b. reflexivity. destruct m.
            inversion H0. inversion H1. inversion H2.
            simpl. split. reflexivity. apply IHx0. simpl in H0. simpl. tauto.
          }
        * simpl in H0. tauto.
        * auto.
    - intros. inversion H0. simpl. destruct a, c.
      + split. auto. apply H. auto. auto.
      + inversion H2. 
      + inversion H2. 
      + inversion H2. destruct x0, y0.
        * apply H. auto. auto.
        * inversion H1.
        * inversion H1.
        * inversion H1. split. auto. apply H. auto. auto. 
  Qed.

  Definition lista_mergeS {A} {AS : Setoid A} := injF2 (@lista_merge A AS) _.

Fixpoint list_delete {A : Type} {AS : Setoid A}  (n : nat) (l : list A) {struct l} : list A :=
  match l with
    | [] => []
    | a' :: l' =>
      match n with
        | O => l'
        | S n' => a' :: list_delete n' l' 
      end
  end
.

Definition lista_delete {A : Type} {AS : Setoid A} {AP : Pointed A} (n : nat)  (l : lista A) : lista A :=
  match l with
    | listaCons _  l' => listaCons _ (list_delete n l')
  end
.

Instance lista_delete_Proper {A : Type} {AS : Setoid A} AP : Proper (equiv ==> equiv ==> equiv ) (@lista_delete A AS AP).
Proof.
  autounfold. intros. destruct x0, y0.  simpl. simpl in H. rewrite H. clear x H. generalize y H0. clear y H0. apply list_ind_2 with (l1:=l) (l2:=l0).
  - intros. reflexivity. 
  - intros. destruct y.
    + simpl. simpl in H0. tauto.
    + simpl. destruct H0. split. auto. apply H. auto.
  - intros. destruct y.
    + simpl. simpl in H0. tauto.
    + simpl. destruct H0. split. auto. apply H. auto.
  - intros. destruct y.
    + simpl. simpl in H0. tauto.
    + simpl. destruct H0. split. auto. apply H. auto.
Qed.

Definition lista_deleteS {A} {AS : Setoid A} {AP : Pointed A} :=
  injF2 (@lista_delete A AS AP) _.
