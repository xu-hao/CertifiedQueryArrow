Require Import Tactics Algebra.Utils SetoidUtils Algebra.SetoidCat Algebra.SetoidCat.ListUtils Algebra.Monad Algebra.SetoidCat.PairUtils Algebra.SetoidCat.MaybeUtils Algebra.SetoidCat.BoolUtils.

Require Import FMapWeakList Coq.Lists.List RelationClasses Relation_Definitions Morphisms SetoidClass.


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
  Parameter St : Setoid t.
  Parameter read : St ~> varS ~~> optionS valS.
  Parameter update : St ~> varS ~~> valS ~~> St.
  Parameter delete : St ~> varS ~~> St.
  Parameter empty : t.
  Parameter dom : St ~> varSetS.
  Notation "store [ var ↦ val ]s " := (update @ store @ var @ val) (at level 11).
  Notation "store [ var ]s " := (read @ store @ var) (at level 11).

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
      delete @ (update @ s @ var @ val) @ var == delete @ s @ var.

  Axiom read_update :
    forall s var val,
      read @ (update @ s @ var @ val) @ var == Some val.

  Axiom update_delete :
    forall s var val,
       (delete @ s @ var) [ var ↦ val ]s == s [ var ↦ val ]s.
  
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
      delete @ (s [ var ↦ val ]s) @ var2 == (delete @ s @ var2) [ var ↦ val ]s.

  Axiom read_delete_diff_var :
    forall s var var2,
      (delete @ s @ var) [var2]s == s[var2]s.

  Axiom read_delete :
    forall s var,
      (delete @ s @ var) [var]s == None.

  Axiom read_empty :
    forall var,
      empty [var]s == None.


End Store.

Module Type Heap.
  Open Scope type_scope.
  Parameter t : Type.
  Parameter St : Setoid t.
  Parameter dom : St ~> valSetS.
  Parameter predDom : predS ~> St ~~> valSetS.
  Parameter preds : St ~> predSetS.
  Parameter newAddr : St ~> (St ~*~ valS).
  Parameter delete : valS ~> St ~~> St.
  Parameter deletePred :  valS ~> predS ~~> St ~~> St.
  Parameter lookupBySPO :  valS ~> predS ~~> valS ~~> St ~~> boolS.
  Parameter lookupBySubject : valS ~> predS ~~> St ~~> optionS valS.
  Parameter lookupByObject : predS ~> valS ~~> St ~~> listS valS.
  Parameter lookupByPred : predS ~> St ~~> listS (valS ~*~ valS).
  Parameter update : valS ~> predS ~~> valS ~~> St ~~> St.
  Parameter empty : t.
  Parameter union : St ~> St ~~> St.

  Axiom eq_heap : forall (h1 h2 : t) , (forall v p, lookupBySubject @ h1 @ v @ p == lookupBySubject @ h2 @ v @ p) -> h1 == h2.

  Definition disjoint : St ~> St ~~> iff_setoid.
   refine (injF2 (fun h1 => fun h2 => (dom @ h1) ∩ (dom @ h2) == ∅) _).
   Lemma disjoint_1 : Proper (equiv ==> equiv ==> equiv)
     (fun h1 h2 : t => (dom @ h1) ∩ (dom @ h2) == ∅).
   Proof.
     repeat     autounfold. intros. destruct dom. simpl in *.  unfold properF in p.
                                                               
     rewrite H, H0. reflexivity.  
   Qed.
   apply disjoint_1.
  Defined.
  
  Notation "heap [ val , pred ]" := (lookupBySubject @ heap @ val @ pred) (at level 11).
  Notation "heap [ val , pred  ↦  val2 ]  " := (update @ heap @ val @ pred @ val2) (at level 11).
  Notation "h1 ⊥ h2" := (disjoint @ h1 @ h2) (at level 15).
  Notation "h1 ⋅ h2" := (union @ h1 @ h2) (at level 15).

  Axiom dom_lookup : forall h val, val ∈ (dom @ h) -> exists pred val2, h [val,pred] == Some val2.

  Axiom dom_domPred : forall h val, val ∈ (dom @ h) -> exists pred, val ∈ (predDom @ h @ pred).

  Axiom domPred_lookup : forall h val pred, val ∈ (predDom @ h @ pred) -> exists val2, h[val, pred] == Some val2.

  Axiom lookupBySubject_empty : forall val pred, empty [val,pred] == None.

  Axiom lookupByObject_empty : forall pred val, lookupByObject @ empty @ pred @ val == List.nil.

  Axiom lookupByPred_empty : forall pred , lookupByPred @ empty @ pred == List.nil.

  Axiom lookupBySPO_empty : forall val pred val2, lookupBySPO @ empty @ val @ pred @ val2 == false.
  
  Axiom lookup_predDom : forall h val pred, (exists val2, lookupBySubject @ h @ val @ pred == Some val2) -> val ∈ (predDom @ h @ pred).

  Axiom predDom_dom : forall h val, (exists pred, val ∈ (predDom @ h @ pred)) -> val ∈ (dom @ h).

  Lemma lookup_dom : forall h val, (exists pred val2, lookupBySubject @ h @ val @ pred == Some val2) -> val ∈ (dom @ h).
  Proof.
    intros. apply predDom_dom. destruct H as [? [? ?]]. exists x. apply lookup_predDom. exists x0.  auto.
  Qed.

  Axiom predDom_newAddr:
        forall h h' val pred, (h', val) == newAddr @ h -> val ∈? (predDom @ h @ pred) == false.
  
  Axiom lookupBySubject_predDom_0:
        forall h val pred, val ∈? (predDom @ h @ pred) == false -> h [val , pred] == None.
  
  Axiom lookupBySubject_predDom_1:
        forall h val pred, val ∈? (predDom @ h @ pred) == true -> exists val2, h [val , pred] == val2.

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
      val ∈? (predDom @ ( h [ val , pred ↦ val2 ]) @ pred) == true.
  
  Axiom predDom_update_diff_addr :
    forall h val val' pred pred' val2,
      val <> val' -> 
      val ∈? (predDom @ ( h [ val' , pred' ↦ val2 ]) @ pred) == val ∈? (predDom @ h @ pred).

  Axiom predDom_update_diff_pred :
    forall h val val' pred pred' val2,
      pred <> pred' -> 
      val ∈? (predDom @ ( h [ val' , pred' ↦ val2 ]) @ pred) = val ∈? (predDom @ h @ pred).

  Axiom dom_update_diff_addr :
    forall h val val' pred val2,
      val <> val' -> 
      val ∈? (dom @ ( h [ val' , pred ↦ val2 ])) == val ∈? (dom @ h).

End Heap.

