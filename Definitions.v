Require Import Tactics Utils Algebra.SetoidUtils Algebra.SetoidCat  Algebra.Monad Algebra.PairUtils Algebra.Maybe Algebra.Alternative Algebra.Functor Algebra.FoldableFunctor Algebra.Applicative.

Require Import FMapWeakList  RelationClasses Relation_Definitions Morphisms SetoidClass.


Module FVarSet := FSetNat.

Module FValSet := FSetNat.

Module FPredSet := FSetNat.

Definition var := nat.

Definition pred := nat.

Definition val := nat.

Definition addr := nat.

Definition builtin := nat.

Program Instance natSetoid : Setoid nat.

Instance varS : Setoid var := natSetoid.
Instance valS : Setoid val := natSetoid.
Instance predS : Setoid pred := natSetoid.
Instance builtinS : Setoid builtin := natSetoid.

Program Instance natSetSetoid : Setoid FSetNat.t :=
  {
    equiv := FSetNat.eq
  }.

Instance varSetS : Setoid FVarSet.t := natSetSetoid.
Instance valSetS : Setoid FValSet.t := natSetSetoid.
Instance predSetS : Setoid FPredSet.t := natSetSetoid.

Module Type Store.
  Parameter t : Type.
  Parameter tS : Setoid t.
  Parameter read : varS ~> tS ~~> optionS valS.
  Parameter update : varS ~> valS ~~> tS ~~> tS.
  Parameter delete : varS ~> tS ~~> tS.
  Parameter emptyStore : t.
  Parameter dom : tS ~> varSetS.
  Notation "store [ var ↦ val ]s " := (update @ var @ val @ store) (at level 11).
  Notation "store [ var ]s " := (read @ var @ store) (at level 11).

  Axiom eq_store : forall s1 s2, (forall v, read @ s1 @ v == read @ s2 @ v) -> s1 == s2.
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
      s [ var ↦ val ]s [ var2 ]s == s [ var2 ]s.

  Axiom update_update_diff_var :
    forall s var var2 val val2,
      s [ var ↦ val ]s [ var2 ↦ val2 ]s == s [ var2 ↦ val2 ]s [ var ↦ val ]s.

  Axiom delete_update_diff_var:
    forall s var var2 val,
      delete @ var2 @ (s [ var ↦ val ]s) == (delete @ var2 @ s) [ var ↦ val ]s.
 
  Axiom read_delete_diff_var :
    forall s var var2,
      (delete @ var @ s) [var2]s == s[var2]s.

  Axiom read_delete :
    forall s var,
      (delete @ var @ s) [var]s == None.

  Axiom read_empty :
    forall var,
      emptyStore [var]s == None.


End Store.

Module Type Heap.
  Open Scope type_scope.
  Parameter t : Type.
  Parameter l : forall A, (Setoid A) -> Type.
  Parameter lS : forall A (AS : Setoid A), Setoid (l A AS).
  Parameter (func : @Functor l lS).
  Parameter (alt : @Alternative l lS).
  Parameter (foldable : @FoldableFunctor l lS func).
  Parameter (app : @Applicative l lS func).
  Parameter tS : Setoid t.
  Parameter dom : tS ~> valSetS.
  Parameter predDom : predS ~> tS ~~> valSetS.
  Parameter preds : tS ~> predSetS.
  Parameter newAddr : tS ~> (tS ~*~ valS).
  Parameter delete : valS ~> tS ~~> tS.
  Parameter deletePred :  valS ~> predS ~~> tS ~~> tS.
  Parameter lookupBySPO :  valS ~> predS ~~> valS ~~> tS ~~> boolS.
  Parameter lookupBySubject : valS ~> predS ~~> tS ~~> optionS valS.
  Parameter lookupByObject : predS ~> valS ~~> tS ~~> lS _ valS.
  Parameter lookupByPred : predS ~> tS ~~> lS _ (valS ~*~ valS).
  Parameter update : valS ~> predS ~~> valS ~~> tS ~~> tS.
  Parameter emptyH : t.
  Parameter union : tS ~> tS ~~> tS.

  Axiom eq_heap : forall (h1 h2 : t) , (forall v p, lookupBySubject @ v @ p @ h1 == lookupBySubject @ v @ p @ h2) -> h1 == h2.

  Definition disjoint : tS ~> tS ~~> iff_setoid.
   refine (injF2 (fun h1 => fun h2 => (dom @ h1) ∩ (dom @ h2) == ∅) _).
   Lemma disjoint_1 : Proper (equiv ==> equiv ==> equiv)
     (fun h1 h2 : t => (dom @ h1) ∩ (dom @ h2) == ∅).
   Proof.
     repeat     autounfold. intros. destruct dom. simpl in *.  
                                                               
     rewrite H, H0. reflexivity.  
   Qed.
   apply disjoint_1.
  Defined.
  
  Notation "heap [ val , pred ]" := (lookupBySubject @ val @ pred @ heap) (at level 11).
  Notation "heap [ val , pred  ↦  val2 ]  " := (update @ val @ pred @ val2 @ heap) (at level 11).
  Notation "h1 ⊥ h2" := (disjoint @ h1 @ h2) (at level 15).
  Notation "h1 ⋅ h2" := (union @ h1 @ h2) (at level 15).

  Axiom dom_lookup : forall h val, val ∈ (dom @ h) -> exists pred val2, h [val,pred] == Some val2.

  Axiom dom_domPred : forall h val, val ∈ (dom @ h) -> exists pred, val ∈ (predDom @ pred @ h).

  Axiom domPred_lookup : forall h val pred, val ∈ (predDom @ pred @ h) -> exists val2, h[val, pred] == Some val2.

  Axiom lookupBySubject_empty : forall val pred, emptyH [val,pred] == None.

  Axiom lookupByObject_empty : forall pred val, lookupByObject @ pred @ val @ emptyH == empty.

  Axiom lookupByPred_empty : forall pred , lookupByPred @ pred @ emptyH == empty.

  Axiom lookupBySPO_empty : forall val pred val2, lookupBySPO @ val @ pred @ val2 @ emptyH == false.
  
  Axiom lookup_predDom : forall h val pred, (exists val2, lookupBySubject @ val @ pred @ h == Some val2) -> val ∈ (predDom @ pred @ h).

  Axiom predDom_dom : forall h val, (exists pred, val ∈ (predDom @ pred @ h)) -> val ∈ (dom @ h).

  Lemma lookup_dom : forall h val, (exists pred val2, lookupBySubject @ val @ pred @ h == Some val2) -> val ∈ (dom @ h).
  Proof.
    intros. apply predDom_dom. destruct H as [? [? ?]]. exists x. apply lookup_predDom. exists x0.  auto.
  Qed.

  Axiom predDom_newAddr:
        forall h h' val pred, (h', val) == newAddr @ h -> val ∈? (predDom @ pred @ h) == false.
  
  Axiom lookupBySubject_predDom_0:
        forall h val pred, val ∈? (predDom @ pred @ h) == false -> h [val , pred] == None.
  
  Axiom lookupBySubject_predDom_1:
        forall h val pred, val ∈? (predDom @ pred @ h) == true -> exists val2, h [val , pred] == val2.

  Lemma lookupBySubject_newAddr:
        forall h h' val pred, (h', val) == newAddr @ h -> h [val, pred] == None.
  Proof.
    intros. apply lookupBySubject_predDom_0. apply predDom_newAddr with (h:=h) (h':=h'). auto.
  Qed.
  
  Axiom lookup_update :
    forall h val pred val2,
      h [ val , pred ↦  val2 ] [ val , pred ] == Some val2.
  
  Axiom lookup_update_diff_addr :
    forall h val val' pred pred' val2,
      val <> val' ->
      h [ val , pred ↦ val2 ] [ val' , pred' ] == h [ val' , pred' ].
  
  Axiom lookup_update_diff_pred :
    forall h val val' pred pred' val2,
      pred <> pred' ->
      h [ val , pred ↦ val2 ] [ val' , pred' ] == h [ val' , pred' ].
  
  Axiom update_update :
    forall h val pred val2 val3,
      h [ val , pred ↦  val2 ] [ val , pred ↦ val3 ] == h  [ val , pred ↦ val3 ].
  
  Axiom predDom_update :
    forall h val pred val2,
      val ∈? (predDom @ pred @ ( h [ val , pred ↦ val2 ])) == true.
  
  Axiom predDom_update_diff_addr :
    forall h val val' pred pred' val2,
      val <> val' -> 
      val ∈? (predDom @ pred @ ( h [ val' , pred' ↦ val2 ])) == val ∈? (predDom @ pred @ h).

  Axiom predDom_update_diff_pred :
    forall h val val' pred pred' val2,
      pred <> pred' -> 
      val ∈? (predDom @ pred @ ( h [ val' , pred' ↦ val2 ])) = val ∈? (predDom @ pred @ h).

  Axiom dom_update_diff_addr :
    forall h val val' pred val2,
      val <> val' -> 
      val ∈? (dom @ ( h [ val' , pred ↦ val2 ])) == val ∈? (dom @ h).

End Heap.

