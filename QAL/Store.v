Require Import FSetInterface.
Require Import Tactics Algebra.Utils SetoidUtils Algebra.SetoidCat  Algebra.Monad Algebra.SetoidCat.PairUtils Algebra.SetoidCat.MaybeUtils Algebra.Monad.Maybe Algebra.Alternative Algebra.Functor Algebra.FoldableFunctor Algebra.Applicative Algebra.Monoid Algebra.SetoidCat.NatUtils Algebra.SetoidCat.BoolUtils Algebra.Monoid.PropUtils QAL.Definitions.

Require Import FMapWeakList  RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Structures.DecidableTypeEx.



Module Type Store (VT : ValType).
  Import VT.
  Parameter t : Type.
  Parameter tS : Setoid t.
  Parameter read : varS ~> tS ~~> optionS valS.
  Parameter update : varS ~> valS ~~> tS ~~> tS.
  Parameter delete : varS ~> tS ~~> tS.
  Parameter emptyStore : t.
  Notation "store [ var ↦ val ]s " := (update @ var @ val @ store) (at level 11).
  Notation "store [ var ]s " := (read @ var @ store) (at level 11).

  Axiom eq_store : forall s1 s2, (forall v, read @ v @ s1 == read @ v @ s2) -> s1 == s2.
  (* Global Program Instance storesSetoid : Setoid (list t) := listS St.  *)

(*  Instance eq_stores_Proper : Proper (eq_stores ==> eq_stores ==> iff) eq_stores.
  Proof.
    apply equiv_equiv_Proper. apply eq_stores_Equivalence.
  Qed.
  
  Instance eq_store_Proper : Proper (eq_store ==> eq_store ==> iff) eq_store.
  Proof.
    apply equiv_equiv_Proper. apply eq_store_Equivalence.
  Qed.
  *)

  Axiom delete_update :
    forall s var val,
      delete @ var @ ( s[ var ↦ val ]s) == delete @ var @ s.

  Axiom read_update :
    forall s var val,
      (s[ var ↦ val ]s) [  var]s == Some val.

  Axiom update_delete :
    forall s var val,
       (delete @ var @ s ) [ var ↦ val ]s == s [ var ↦ val ]s.
  
  Axiom update_update :
    forall s var val val2,
      s [ var ↦ val ]s [ var ↦ val2 ]s == s [ var ↦ val2 ]s.
  
  Axiom read_update_diff_var :
    forall s var var2 val,
      var <> var2 ->
      s [ var ↦ val ]s [ var2 ]s == s [ var2 ]s.

  Axiom update_update_diff_var :
    forall s var var2 val val2,
      var <> var2 ->
      s [ var ↦ val ]s [ var2 ↦ val2 ]s == s [ var2 ↦ val2 ]s [ var ↦ val ]s.

  Axiom delete_update_diff_var:
    forall s var var2 val,
      var <> var2 ->
      delete @ var2 @ (s [ var ↦ val ]s) == (delete @ var2 @ s) [ var ↦ val ]s.
 
  Axiom read_delete_diff_var :
    forall s var var2,
      var <> var2 ->
      (delete @ var @ s) [var2]s == s[var2]s.

  Axiom read_delete :
    forall s var,
      (delete @ var @ s) [var]s == None.

  Axiom read_empty :
    forall var,
      emptyStore [var]s == None.


End Store.

