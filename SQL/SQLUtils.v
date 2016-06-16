Require Import Definitions Algebra.Monoid Expr Algebra.SetoidCat Algebra.SetoidCat.MaybeUtils Algebra.Monad.Maybe Tactics Algebra.SetoidCat.ListUtils Algebra.Functor Algebra.Applicative Algebra.Alternative Algebra.FoldableFunctor Algebra.SetoidCat.PairUtils Algebra.Monad Algebra.Lens.Lens Algebra.Lens.MaybeLens ListLens Utils SetoidUtils SQL Pointed Lista Matrixp GenUtils Algebra.Monoid.MaybeUtils Algebra.SetoidCat.NatUtils.
Require Import Coq.Structures.DecidableTypeEx List SetoidClass PeanoNat FMapWeakList Basics Coq.Arith.Compare_dec.

Existing Instance maybe_Monad.
Instance maybeFunctor : @Functor maybe (@maybeS) := monadFunctor.
Instance maybe_Applicative : @Applicative maybe (@maybeS) _ := monad_Applicative.
Existing Instance maybe_mappend_PointedFunction2.

Definition unionRows : listaS (maybeS rowS) ~> listaS (maybeS rowS) ~~> listaS (maybeS rowS) :=
  lista_zipWithS maybe_first_mappend.

Definition minS := injF2 min _.

Existing Instance sqlVal_Pointed.

Definition _unionTables (tab1 tab2 : matrixp sqlVal) : matrixp sqlVal :=
  matrixpConsS @ (unionRows @ (tableRowsGetter @ tab1) @ (tableRowsGetter @ tab2)).

Instance _unionTables_Proper : Proper (equiv ==> equiv ==> equiv) _unionTables.
Proof.
  autounfold. intros. unfold _unionTables. rewritesr.
Qed.

Definition unionTables := injF2 _unionTables _.

Definition unionDatabases : databaseS ~> databaseS ~~> databaseS :=
  list_zipWithS' @ unionTables.



Definition caseSqlVal {A} {AS : Setoid A} (nat1 : natS ~> AS) (addr1 : natS ~*~ natS ~> AS) (func1 : sqlFuncS ~> AS) (nil1 : A) (row1 : sqlValS ~> sqlValS ~~> AS) val1 : A :=
  match val1 with
    | vNat n => nat1 @ n
    | vAddr n => addr1 @ n
    | vFunc a => func1 @ a
    | vRow a b => row1 @ a @ b
    | vNil => nil1
  end
.

Instance caseSqlVal_Proper A AS : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv ==> equiv ==> equiv) (@caseSqlVal A AS).
Proof.
  autounfold. intros. simpl in H4.  rewrite H4. induction y4.
  - simpl. rewritesr.
  - simpl. rewritesr.
  - auto. 
  - simpl. rewritesr.
  - simpl. rewritesr. 
Qed.

Definition caseSqlValS {A AS} := injF6 (@caseSqlVal A AS) _.

Definition extractAddrS : sqlValS ~> maybeS (natS ~*~ natS) :=
  caseSqlValS
    @ (constS _ @ None)
    @ (SomeS)
    @ (constS _ @ None)
    @ None
    @ (constS _ @ (constS _ @ None)).

Definition extractNatS : sqlValS ~> maybeS natS :=
  caseSqlValS
    @ (SomeS)
    @ (constS _ @ None)
    @ (constS _ @ None)    @ None
    @ (constS _ @ (constS _ @ None)).

Instance vNat_Proper : Proper (equiv ==> equiv) vNat.
Proof.
  solve_proper.    
Qed.

Definition vNatS : natS ~> sqlValS := injF vNat _.

Instance vAddr_Proper : Proper (equiv ==> equiv) vAddr.
Proof.
  autounfold. intros. destruct x,y. simpl in *. f_equal. f_equal. tauto.  tauto. 
Qed.

Definition vAddrS : sqlAddrS ~> sqlValS := injF vAddr _.


Lemma row_equiv_dec : forall (r1 r2 : row) ,  {r1 == r2} + {~r1 == r2}.
Proof.
  intros. apply lista_equiv_dec.  apply SQLValType.equiv_dec.
Defined.

Lemma maybe_row_equiv_dec : forall r1 r2 : maybe row, {r1 == r2} + {~r1 == r2}.
Proof.
  intros. apply maybe_equiv_dec. apply row_equiv_dec. 
Defined.

  
