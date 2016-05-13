Require Import FSetInterface.
Require Import Tactics Utils Algebra.SetoidUtils Algebra.SetoidCat  Algebra.Monad Algebra.PairUtils Algebra.Maybe Algebra.Alternative Algebra.Functor Algebra.FoldableFunctor Algebra.Applicative.

Require Import FMapWeakList  RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Structures.DecidableTypeEx.


Module FVarSet := FSetNat.

Module FValSet := FSetNat.

Module FPredSet := FSetNat.

Definition var := nat.

Definition pred := nat.

Definition type := nat.

Instance varS : Setoid var := natS.
Instance predS : Setoid pred := natS.
Instance typeS : Setoid type := natS.

Program Instance natSetSetoid : Setoid FSetNat.t :=
  {
    equiv := FSetNat.eq
  }.

Instance varSetS : Setoid FVarSet.t := natSetSetoid.
Instance predSetS : Setoid FPredSet.t := natSetSetoid.


Module WSNotations (VT : WS).
  Notation "∅" := VT.empty.
  Notation "a ∩ b" := (VT.inter a b) (at level 11, left associativity).
  Notation "a ∪ b" := (VT.union a b) (at level 12, left associativity).
  Notation "﹛ a ﹜" := (VT.singleton a) (at level 10).
  Notation "a ∈ b" := (VT.In a b) (at level 15).
  Notation "a ∈? b" := (VT.mem a b) (at level 15).

End WSNotations.

Module Type ValType.
  Parameter val : Type.
  Parameter valS : Setoid val.
  Axiom equiv_dec : forall val1 val2, {val1 == val2} + {~ val1 == val2}.
End ValType.


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

Module Type Heap (VT : ValType).
  Import VT.
  Open Scope type_scope.
  Parameter t : Type.
  Parameter tS : Setoid t.
  Parameter predOfType : predS ~> typeS ~~> tS ~~> iff_setoid.
  Parameter typeOfHeap : typeS ~> tS ~~> iff_setoid.
  Parameter newAddr : typeS ~> tS ~~> optionS (tS ~*~ valS).
  Parameter allocated : valS ~> tS ~~> iff_setoid.
  Parameter update : valS ~> predS ~~> valS ~~> tS ~~> tS.
  Parameter delete : valS ~> tS ~~> tS.
  Parameter emptyH : t.
  Parameter readType : valS ~> tS ~~> optionS typeS.
  Parameter read : valS ~> predS ~~> tS ~~> optionS valS.
  Parameter union : tS ~> tS ~~> tS.
  Parameter l : forall A, (Setoid A) -> Type.
  Parameter lS : forall A (AS : Setoid A), Setoid (l A AS).
  Parameter (func : @Functor l lS).
  Parameter (alt : @Alternative l lS).
  Parameter (foldable : @FoldableFunctor l lS func).
  Parameter (app : @Applicative l lS func).
  Parameter lookupByObject : predS ~> valS ~~> tS ~~> lS _ valS.
  Parameter lookupByPred : predS ~> tS ~~> lS _ (valS ~*~ valS).

  Notation "heap [ val , pred ]" := (read @ val @ pred @ heap) (at level 11).
  Notation "heap [ val , pred  ↦  val2 ]  " := (update @ val @ pred @ val2 @ heap) (at level 11).

  Axiom eq_heap : forall (h1 h2 : t) ,
                    (forall v, allocated @ v @ h1 == allocated @ v @ h2) ->
                    (forall v p, read @ v @ p @ h1 == read @ v @ p @ h2) ->
                    (forall p t, predOfType @ p @ t @ h1 <-> predOfType @ p @ t @ h2) ->
                    (forall t, typeOfHeap @ t @ h1 <-> typeOfHeap @ t @ h2) ->
                    h1 == h2.

  Axiom read_empty : forall val pred, emptyH [val,pred] == None.

  Axiom read_newAddr_1:
        forall h type1 pred1 addr h', Some (h', addr) == newAddr @ type1 @ h -> read @ addr @ pred1 @ h == None.
  
  Axiom read_newAddr_2:
    forall h type1 pred1 addr h', Some (h', addr) == newAddr @ type1 @ h -> read @ addr @ pred1 @ h' == None.

  Axiom read_1 :
    forall h val pred,
      readType @ val @ h == None -> 
      h [ val , pred ] == None.

  Axiom read_2 :
    forall h val pred t,
      readType @ val @ h == Some t -> 
      ~ predOfType @ pred @ t @ h ->
      h [ val , pred ] == None.

  Axiom read_update :
    forall h val pred val2 t,
      readType @ val @ h == Some t -> 
      predOfType @ pred @ t @ h ->
      h [ val , pred ↦  val2 ] [ val , pred ] == Some val2.
  
  Axiom read_update_diff_addr :
    forall h val val' pred pred' val2,
      val <> val' ->
      h [ val , pred ↦ val2 ] [ val' , pred' ] == h [ val' , pred' ].
  
  Axiom read_update_diff_pred :
    forall h val val' pred pred' val2,
      pred <> pred' ->
      h [ val , pred ↦ val2 ] [ val' , pred' ] == h [ val' , pred' ].
  
  Axiom update_update :
    forall h val pred val2 val3,
      h [ val , pred ↦  val2 ] [ val , pred ↦ val3 ] == h  [ val , pred ↦ val3 ].
  
End Heap.

Module HeapUtils (VT : ValType) (H : Heap VT).
  Import VT H.

  Definition lookupBySPO :  valS ~> predS ~~> valS ~~> tS ~~> boolS.
    simple refine (injF4 (fun addr1 pred1 val1 h =>
                            match h[addr1, pred1] with
                              | Some val2 => if equiv_dec val1 val2 then true else false
                              | None => false
                            end) _).
    Lemma lookupBySPO_1 : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv)
     (fun (addr1 : val) (pred1 : pred) (val1 : val) (h : t) =>
      match h [addr1, pred1] with
      | Some val2 => if equiv_dec val1 val2 then true else false
      | None => false
      end).
    Proof.
      autounfold. intros. matchequiv. simpl in H3. destruct (equiv_dec x1 v). destruct (equiv_dec y1 v0). reflexivity. destruct n. transitivity x1. symmetry. auto. transitivity v. auto. auto. destruct (equiv_dec y1 v0). destruct n. transitivity y1. auto. transitivity v0. auto. symmetry. auto. reflexivity.
    Qed.
    apply lookupBySPO_1.
  Defined.
    

  Definition inDom : valS ~> tS ~~> iff_setoid.
    simple refine (injF2 (fun addr h => exists pred1 a, read @ addr @ pred1 @ h == Some a) _).
    apply optionS.
    apply valS.
    Lemma inDom_1 : Proper (equiv ==> equiv ==> equiv)
     (fun (addr : val) (h : t) =>
        exists (pred1 : pred) (a : val), h [addr, pred1] == Some a).
    Proof.
      solve_proper.
    Qed.
    apply inDom_1.
  Defined.

  Definition disjoint : tS ~> tS ~~> iff_setoid.
   refine (injF2 (fun h1 h2 => forall addr, ~(inDom @ addr @ h1) \/ ~ (inDom @ addr @ h2)) _).
   Lemma disjoint_1 : Proper (equiv ==> equiv ==> equiv)
     (fun h1 h2 => forall addr, ~(inDom @ addr @ h1) \/ ~ (inDom @ addr @ h2)).
   Proof.
     solve_proper.     
   Qed.
   apply disjoint_1.
  Defined.

  Definition singleton : valS ~> predS ~~> valS ~~> tS ~~> iff_setoid.
    simple refine (injF4 (fun addr1 pred1 val1 h =>
                            h [ addr1 , pred1 ] == Some val1 /\
                            forall addr2 pred2 val2,
                              h [ addr2 , pred2 ] == Some val2 ->
                              addr1 == addr2 /\
                              pred1 == pred2 /\
                              val2 == val1) _).
    apply optionS.
    apply valS.
    apply optionS.
    apply valS.
    apply valS.
    apply predS.
    apply valS.
    Lemma singleton_1 : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv)
     (fun (addr1 : val) (pred1 : pred) (val1 : val) (h : t) =>
      h [addr1, pred1] == Some val1 /\
      (forall (addr2 : val) (pred2 : pred) (val2 : val),
       h [addr2, pred2] == Some val2 ->
       addr1 == addr2 /\ pred1 == pred2 /\ val2 == val1)).
    Proof.
      autounfold. intros. rewrites. split.
      intros. destruct H3. split.
      rewrite H3. simpl. auto.
      intros. rewrite <- H1, <- H.  apply H4. rewrite H2. auto.
      intros. destruct H3. split.
      rewrite H3. simpl. symmetry. auto.
      intros. rewrite H1, H.  apply H4. rewrite <- H2. auto.
    Qed.
    apply singleton_1.
  Defined.
  
  Notation "heap [ val , pred ]" := (read @ val @ pred @ heap) (at level 11).
  Notation "heap [ val , pred  ↦  val2 ]  " := (update @ val @ pred @ val2 @ heap) (at level 11).
  Notation "h1 ⊥ h2" := (disjoint @ h1 @ h2) (at level 15).
  Notation "h1 ⋅ h2" := (union @ h1 @ h2) (at level 15).

End HeapUtils.
