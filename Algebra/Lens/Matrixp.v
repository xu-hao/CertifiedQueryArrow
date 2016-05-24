Require Import Algebra.Functor Algebra.Applicative Algebra.SetoidCat Algebra.ListUtils Algebra.PairUtils Algebra.Maybe Algebra.SetoidUtils Algebra.Monad Algebra.Maybe Tactics Utils Algebra.Lens.Lista Pointed.

Require Import SetoidClass List Coq.Classes.RelationClasses Coq.Arith.PeanoNat Coq.Arith.Compare_dec.



(* partial matrix *)

Inductive matrixp A  {AS : Setoid A}{AP : Pointed A}: Type := matrixpCons : lista (maybe (lista A)) -> matrixp A. 


Existing Instance maybe_Monad.
Existing Instance monadFunctor.
Definition _rows  {A : Type} {AS : Setoid A} {AP : Pointed A} (mat : matrixp A) : lista (maybe (lista A)) := match mat with
                     | matrixpCons _ rows => rows
                   end.


Definition matrixp_equiv {A} {AS : Setoid A} {AP : Pointed A} (m1 m2 : matrixp A) : Prop :=
  match m1, m2 with
    | matrixpCons _ l, matrixpCons _ l0 =>
      l == l0
  end.


Hint Unfold matrixp_equiv.

Instance matrixp_equiv_Equivalence {A} {AS : Setoid A} AP : Equivalence (@matrixp_equiv A AS AP).
Proof.
  split.
  - autounfold. intros. destruct x. reflexivity. 
  - autounfold. intros. destruct x, y. symmetry. auto. 
  - autounfold. intros. destruct x, y, z. transitivity l0. auto.
auto.
Qed.


Instance matrixpS {A} (AS : Setoid A) {AP : Pointed A}: Setoid (matrixp A) :=
  {
    equiv := matrixp_equiv
  }
.

Instance _rows_Proper A (AS : Setoid A) AP : Proper (equiv ==> equiv) (@_rows A AS AP).
Proof.
  autounfold. intros. destruct x, y, l, l0. unfold _rows. simpl in H.  auto. 
Qed.

Definition rows {A : Type} {AS : Setoid A} {AP} := injF (@_rows A AS AP) _.

Instance matrixpCons_Proper {A : Type} {AS : Setoid A} AP : Proper ( equiv ==> equiv) (@matrixpCons A AS AP ).
Proof.
  autounfold. intros. simpl. auto.
Qed.

(* read matrix column *)


Definition _readCol {A : Type} {AS : Setoid A} {AP : Pointed A} ( n : nat) (l : maybe (lista A)) :=
    match l with
      | None => None
      | Some l' => Some (lista_nth n l')
    end.
  
Instance _readCol_Proper {A : Type} {AS : Setoid A} AP : Proper (equiv ==> equiv ==> equiv) (@_readCol A AS AP).
Proof.
  autounfold. intros. unfold _readCol. simpl in H. rewrite H. clear x H. matchequiv. simpl in H.  simpl. rewrite H. reflexivity. 
Qed.

Definition readCol {A : Type} {AS : Setoid A} {AP} := injF2 (@_readCol A AS AP) _. 

Instance readCol_PointedFunction {A : Type} {AS : Setoid A} {AP : Pointed A} n : PointedFunction (@readCol A AS AP @ n).
Proof.
  split. reflexivity.  
Qed.

Definition _readWholeCol {A} {AS : Setoid A} {AP : Pointed A} n l :=
   (lista_mapS (readCol @ n) @ l).

Instance _readWholeCol_Proper {A : Type} {AS : Setoid A} AP : Proper (equiv ==> equiv ==> equiv) (@_readWholeCol A AS AP).
Proof.
  autounfold. intros. unfold _readWholeCol. simpl in H, H0. rewrite H, H0.  rewritesr.  
Qed.

Definition readWholeCol {A : Type} {AS : Setoid A} {AP} := injF2 (@_readWholeCol A AS AP) _. 


Definition _readMatrixCol {A : Type} {AS : Setoid A} {AP : Pointed A} n mat :=
  match mat with
    | matrixpCons _ l => readWholeCol @ n @ l
  end.

Instance _readMatrixCol_Proper {A} {AS : Setoid A} AP : Proper (equiv ==> equiv ==> equiv) (@_readMatrixCol A AS AP).
Proof.
  autounfold. intros. destruct x0, y0. unfold _readMatrixCol. rewrite H. simpl in H0. rewrite H0. reflexivity. 
Qed.

Definition readMatrixCol {A : Type} {AS : Setoid A} {AP} := injF2 (@_readMatrixCol A AS AP) _.

(*
Definition _updateCol {A : Type} {AS : Setoid A} n (l: maybe (lista A)) (a : maybe A) :=
  match l, a with
    | None, _ => None
    | _, None => l
    | Some l', Some a' => Some (lista_updateS @ n @ l' @ a')
  end
.

Instance _updateCol_Proper {A : Type} {AS : Setoid A} : Proper (equiv ==> equiv ==> equiv ==> equiv) (@_updateCol A AS).
Proof.
  autounfold. intros. unfold _updateCol. matchequiv. matchequiv. simpl in H0, H1. rewrite H, H0, H1. reflexivity. auto.  
Qed.

Definition updateCol {A : Type} {AS : Setoid A} := injF3 (@_updateCol A AS) _.

Definition updateWholeCol {A : Type} {AS : Setoid A} n : listaS (maybeS (listaS AS)) ~> listaS (maybeS AS) ~~> listaS (maybeS (listaS AS)) :=
  lista_zipWithS @ (updateCol @ n).



Definition _updateMatrixCol {A : Type} {AS : Setoid A}  n mat col  :=
  match mat with
    | matrixpCons _ l => matrixpCons _  (updateWholeCol n @ l @ col)
  end.

Hint Unfold _updateMatrixCol.
*)

(*Lemma matrixp_equiv_cons : forall {A : Type} {AS : Setoid A} w (a1 a2 : A) (a b : maybe (list A)) (la lb : list (maybe (list A))), matrixp_equiv0 w (a::la) (b::lb) = lista_equiv w (listaCons a1 a) (listaCons a2 b) /\ matrixp_equiv0 w a1 a2 la lb.

Proof.
  intros. reflexivity.
Qed.*)

(*
Instance _updateMatrixCol_Proper {A} {AS : Setoid A} : Proper (equiv ==> equiv ==> equiv ==> equiv) (@_updateMatrixCol A AS ).
Proof.
  autounfold. intros. destruct x0, y0. destruct x1, y1.  destruct l, l0. Opaque lista_equiv. simpl in H0. rewrite H, H0, H1. reflexivity.
Qed.

Definition updateMatrixCol {A} {AS : Setoid A} := injF3 (@_updateMatrixCol A AS) _.
*)
Definition matrixpConsS {A : Type} {AS : Setoid A} {AP : Pointed A}:= injF (matrixpCons A) _.