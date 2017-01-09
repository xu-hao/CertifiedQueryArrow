Require Import Algebra.Utils Algebra.Monad SetoidUtils Algebra.SetoidCat.ListUtils Algebra.SetoidCat Algebra.Monad.StoreHeap Algebra.Monad.ContT Algebra.NearSemiRing Algebra.Monoid Tactics QAL.Definitions Algebra.FoldableFunctor Algebra.SetoidCat.PairUtils Algebra.Functor Algebra.Alternative Algebra.SetoidCat.MaybeUtils Algebra.Monad.Maybe Algebra.Applicative Algebra.SetoidCat.BoolUtils Algebra.SetoidCat.UnitUtils Algebra.Monoid.BoolUtils Algebra.Monoid.Alternative Algebra.Alternative.List Algebra.Functor.List Algebra.FoldableFunctor.List Algebra.Monad.Utils QAL.Concrete.Definitions QAL.AbstractStore QAL.AbstractHeap QAL.Command Algebra.Traversable.List Algebra.Functor.Monad Algebra.Applicative.Monad.

Require Import Coq.Lists.List PeanoNat RelationClasses Relation_Definitions Morphisms Coq.Program.Basics SetoidClass.

Module Type BuiltInCommand (PT : PredType) (VT : ValType) (S : AbstractStore VT) (H : AbstractHeap PT VT).
  Module TS := Types PT VT S H.
  Import TS.
  Parameter builtInCommand : Type.
  Parameter builtInCommandS : Setoid builtInCommand.
  Parameter freeVarsBuiltInCommand : builtInCommandS ~> varSetS.
  Parameter interpretBuiltInCommand : builtInCommandS ~> stateS unitS.
End BuiltInCommand.

Module Type Literal (VT : ValType).
  Import VT.
  Parameter literal : Type.
  Parameter literalS : Setoid literal.
  Parameter interpretLiteral : literalS ~> valS.
End Literal.

Section PrimitiveCommand.

  Context
    {literal : Type}
    {pred : Type}
    {builtin : Type}.
  
  Inductive term :=
  | termVar : var -> term
  | termVal : literal -> term
  .

  Program Instance termS : Setoid term.

  Inductive qalPrimitiveCommand :=
  | pcBuiltIn : builtin -> qalPrimitiveCommand
  | pcInsert : pred -> list term -> qalPrimitiveCommand
  | pcDelete : pred -> list term -> qalPrimitiveCommand
  | pcInsertProp : pred -> list term -> list term -> qalPrimitiveCommand
  | pcDeleteProp : pred -> list term -> list term -> qalPrimitiveCommand
  | pcAtomic : pred -> list term -> qalPrimitiveCommand
  .

  Program Instance qalPrimitiveCommandS : Setoid qalPrimitiveCommand.

End PrimitiveCommand.

Import FSetNatNotations. 
Module QALPrimitiveCommand (PT : PredType) (VT : ValType)
       (L : Literal VT) (S : AbstractStore VT) (H : AbstractHeap PT VT) (BC : BuiltInCommand PT VT S H) : PrimitiveCommand PT VT S H.
  Open Scope type_scope.
  Module TS := Types PT VT S H.
  Module CA := CommandAux PT VT S H.
  Import PT VT L S H BC TS CA.

  Definition _termFreeVars (t : (@term literal)) : FVarSet.t :=
    match t with
        | termVal _ => ∅
        | termVar v => ﹛ v ﹜ 
    end
  .
  
  Existing Instance termS.

  Instance _termFreeVars_Proper : Proper (equiv ==> equiv) _termFreeVars.
  Proof.
    solve_proper.
  Qed.

  Definition termFreeVars := injF _termFreeVars _.


  Definition tlFreeVars (tl : list term) :=
            fold_right (fun t  fv =>
                      (termFreeVars @ t) ∪ fv) ∅ tl
  .

  Definition _qalPrimitiveCommandFreeVars (pc : @qalPrimitiveCommand literal pred builtInCommand) : FVarSet.t :=
    match pc with
      | pcBuiltIn b => freeVarsBuiltInCommand @ b
      | pcInsert _ tl => tlFreeVars tl
      | pcDelete _ tl => tlFreeVars tl
      | pcInsertProp _ ktl ptl => tlFreeVars ktl ∪ tlFreeVars ptl
      | pcDeleteProp _ ktl ptl => tlFreeVars ktl ∪ tlFreeVars ptl
      | pcAtomic _ tl => tlFreeVars tl
    end
  .

  Existing Instance qalPrimitiveCommandS.
  Instance _qalPrimitiveCommandFreeVars_Proper : Proper (equiv ==> equiv) _qalPrimitiveCommandFreeVars.
   Proof.
    solve_proper.
  Qed.

  Definition qalPrimitiveCommandFreeVars := injF _qalPrimitiveCommandFreeVars _.

  Definition freeVarsPrimitiveCommand := qalPrimitiveCommandFreeVars.

  Definition qalTerm := @term literal.
  Instance qalTermS : Setoid qalTerm := @termS literal.

  Instance argumentVal_Proper : Proper (equiv ==> equiv) (argumentVal val).
  Proof.
    unfold Proper, respectful. intros. auto. 
  Qed.
  
  Definition argumentValS := injF (argumentVal val) _.
  Definition _evalTerm (t : term) : state (argument val) :=
    match t with
      | termVal l => ret @ (argumentValS @ (interpretLiteral @ l))
      | termVar v => getStore >>= ret ∘ (caseMaybeS @ argumentValS @ argumentVar val v) ∘ (S.read @ v)  
    end
  .

  Instance _evalTerm_Proper : Proper (equiv ==> equiv) _evalTerm.
  Proof.
    solve_proper.
  Qed.

  Definition evalTerm := injF _evalTerm _.

  Existing Instance sh_Monad.
  Existing Instance monadFunctor.
  Existing Instance monad_Applicative.
  Definition evalTermList : listS (@termS literal) ~> stateS (listS (argumentS _ valS)) := mapM @ evalTerm.

  Definition _evalTermVal (t : term) : state ( val) :=
    match t with
      | termVal l => ret @ (interpretLiteral @ l)
      | termVar v => getStore >>= ret ∘ (S.read @ v) >>= stopNone  
    end
  .

  Instance _evalTermVal_Proper : Proper (equiv ==> equiv) _evalTermVal.
  Proof.
    solve_proper.
  Qed.

  Definition evalTermVal := injF _evalTermVal _.

  Definition evalTermListVal : listS (@termS literal) ~> stateS (listS valS) := mapM @ evalTermVal.


  Definition updateStore2 : listS (varS ~*~ valS) ~> S.tS ~~> S.tS :=
    flipS @ (fold_rightS @ (uncurryS @ S.update)).
  
  Definition _unionWithCurrStore (s : list (var * val)) : state unit :=
    updateStore @ (updateStore2 @ s).

  Instance _unionWithCurrStore_Proper : Proper (equiv ==> equiv) _unionWithCurrStore.
  Proof.
    solve_properS _unionWithCurrStore.
  Qed.
  
  Definition unionWithCurrStore : listS (varS ~*~ valS) ~> stateS unitS := injF _unionWithCurrStore _.

  Definition _lookupAtom (p : pred) (tl : list (@term literal)) : state (H.l (list (var * val)) _) :=
    (H.lookup @ p)
        <$> (evalTermList @ tl)
        <*> getHeap.

  Instance _lookupAtom_Proper : Proper (equiv ==> equiv ==> equiv) _lookupAtom.
  Proof.
    solve_properS _lookupAtom.
  Qed.
  Definition lookupAtom := injF2 _lookupAtom _.

  Section LookupGeneric.
    Context (p : pred) (tl : list (@term literal)).

    Definition lookupGeneric : state unit :=
      lookupAtom @ p @ tl >>= branchVal >>= unionWithCurrStore.
  End LookupGeneric.
  Instance lookupGeneric_Proper : Proper (equiv ==> equiv ==> equiv) lookupGeneric.
  Proof.
    solve_properS lookupGeneric.    
  Qed.

  
  Section InsertGeneric.
    Context
      (p : pred) (tl : list (@term literal)).

    Definition insertGeneric : state unit :=
      (H.insert @ p
         <$> (evalTermListVal @ tl)
         <*> getHeap) >>= stopNone >>= putHeap.
  End InsertGeneric.
  Instance insertGeneric_Proper : Proper (equiv ==> equiv ==> equiv) insertGeneric.
  Proof.
    solve_properS insertGeneric.
  Qed.

  Section DeleteGeneric.
    Context
      (p : pred) (tl : list (@term literal)).

    Definition deleteGeneric : state unit :=
      (H.delete @ p
         <$> evalTermListVal @ tl 
         <*> getHeap) >>= stopNone >>= putHeap.
  End DeleteGeneric.

  Instance DeleteGeneric_Proper : Proper (equiv ==> equiv ==> equiv) deleteGeneric.
  Proof.
    solve_properS deleteGeneric.
  Qed.

  Section InsertPropGeneric.
    Context
      (p : pred) (ktl ptl : list (@term literal)).

    Definition insertPropGeneric : state unit :=
      (H.insertProp @ p
         <$> (evalTermListVal @ ktl)
         <*> (evalTermListVal @ ptl)
         <*> getHeap) >>= stopNone >>= putHeap.
  End InsertPropGeneric.
  Instance insertPropGeneric_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) insertPropGeneric.
  Proof.
    solve_properS insertPropGeneric.
  Qed.

  Section DeletePropGeneric.
    Context
      (p : pred) (ktl ptl : list (@term literal)).

    Definition deletePropGeneric : state unit :=
      (H.deleteProp @ p
         <$> (evalTermListVal @ ktl)
         <*> (evalTermListVal @ ptl)
         <*> getHeap) >>= stopNone >>= putHeap.
  End DeletePropGeneric.

  Instance DeletePropGeneric_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) deletePropGeneric.
  Proof.
    solve_properS deletePropGeneric.
  Qed.

  Fixpoint _reduce (pc : qalPrimitiveCommand)  : state unit :=
    match pc with
      | pcBuiltIn b =>
        interpretBuiltInCommand @ b
      | pcInsert pred tl =>
        insertGeneric pred tl
      | pcDelete pred tl =>
        deleteGeneric pred tl
      | pcInsertProp pred ktl ptl =>
        insertPropGeneric pred ktl ptl
      | pcDeleteProp pred ktl ptl =>
        deletePropGeneric pred ktl ptl
      | pcAtomic pred tl =>
        lookupGeneric pred tl
    end
  .
  
  Definition reduce : (@qalPrimitiveCommandS literal pred builtInCommand ) ~> stateS unitS := injF _reduce _.
  Definition primitiveCommand := @qalPrimitiveCommand literal pred builtInCommand .
  Definition primitiveCommandS := @qalPrimitiveCommandS literal pred builtInCommand.
  Definition interpretPrimitiveCommand := reduce.
End QALPrimitiveCommand.
