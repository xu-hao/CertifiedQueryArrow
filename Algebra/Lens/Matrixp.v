Require Import Algebra.Functor Algebra.Applicative Algebra.SetoidCat Algebra.ListUtils Algebra.PairUtils Algebra.Maybe Algebra.SetoidUtils Algebra.Monad Algebra.Maybe Tactics Utils VectorUtils Algebra.Lens.LensTypes Algebra.Pointed Algebra.Lens.Lista.

Require Import SetoidClass List Coq.Classes.RelationClasses Coq.Arith.PeanoNat Coq.Arith.Compare_dec.



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