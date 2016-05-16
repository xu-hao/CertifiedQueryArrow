Require Import Definitions Algebra.Monoid  Algebra.SetoidCat Algebra.Maybe Tactics Algebra.ListUtils Algebra.Functor Algebra.Applicative Algebra.Alternative Algebra.FoldableFunctor Algebra.PairUtils Algebra.Maybe Algebra.Monad Algebra.Lens.Lens ListLens MaybeLens Utils SetoidUtils MonoidUtils Pointed Lista Matrixp.
Require Import Coq.Structures.DecidableTypeEx List  SetoidClass PeanoNat FMapWeakList Basics Coq.Init.Specif.

Module FMapNat := FMapWeakList.Make Nat_as_DT.
Module NatNat_as_DT := PairDecidableType Nat_as_DT Nat_as_DT.
Module FMapNatNat := FMapWeakList.Make NatNat_as_DT.

Definition singleton {T} (k : nat) (v : T) : FMapNat.t T :=
  FMapNat.add k v (FMapNat.empty T).

Definition sqlPred := nat (* table index *) * nat (* col index *).

Instance sqlPredS : Setoid sqlPred := natS ~*~ natS.

Definition sqlType := nat (* table index *).

Instance sqlTypeS : Setoid sqlType := natS.

Definition sqlAddr := nat (* table index *) * nat (* row index *).

Instance sqlAddrS : Setoid sqlAddr := natS ~*~ natS.

Inductive sqlVal :=
| vNat : nat -> sqlVal
| vAddr : sqlAddr -> sqlVal
| vRow : list sqlVal -> sqlVal
.

Program Instance sqlValS : Setoid sqlVal.

Module SQLValType <: ValType.
  Definition val := sqlVal.
  Instance valS : Setoid sqlVal :=
    {
      equiv := eq
    }.
  Fixpoint equiv_dec val1 val2 : {val1 == val2} + {~ val1 == val2}.
  Proof.
    destruct val1, val2.
    destruct (Nat.eq_dec n n0). left. congruence.
    right. congruence.
    right. intro. inversion H.
    right. intro. inversion H.
    right. intro. inversion H.
    destruct s as [n n0], s0 as [n1 n2].
    destruct (Nat.eq_dec n n1), (Nat.eq_dec n0 n2). left. congruence.
    right. intro. inversion H. tauto.
    right. intro. inversion H. tauto.
    right. intro. inversion H. tauto.
    right. intro. inversion H.
    right. intro. inversion H.
    right. intro. inversion H.
    destruct (list_eq_dec equiv_dec l l0).
    left. congruence.
    right. congruence.
  Qed.
End SQLValType.

Definition sqlBuiltIn := nat.

Section SQLSyntax.
  

  Inductive sqlExpr :=
  | sqlValExpr : sqlVal -> sqlExpr
  | sqlVarExpr : var -> sqlExpr
  | sqlAppExpr : sqlBuiltIn -> list sqlExpr -> sqlExpr
  | sqlColExpr : sqlExpr -> nat (* col index *) -> sqlExpr
  .

  Program Instance sqlExprS : Setoid sqlExpr. 

  Inductive sqlFormula :=
  | sqlBuiltInFormula : sqlBuiltIn -> list sqlExpr -> sqlFormula
  | sqlAnd : sqlFormula -> sqlFormula -> sqlFormula
  | sqlOr : sqlFormula -> sqlFormula -> sqlFormula
  | sqlNot : sqlFormula -> sqlFormula
  | sqlExists : sql -> sqlFormula
  with
  sql :=
  | sqlQuery : list sqlExpr -> list (sqlTableExpr * var) -> sqlFormula -> sql
  with
  sqlTableExpr :=
  | sqlTable : nat (* table index *) -> sqlTableExpr
  | sqlSelect : sql -> sqlTableExpr
  .

  Program Instance sqlFormulaS : Setoid sqlFormula.
  
  Inductive sqlStmt :=
  | sqlQueryStmt : sql -> sqlStmt
  | sqlInsertStmt : nat (* table index *) -> sql -> sqlStmt
  | sqlUpdateStmt : nat -> nat (* col index *) -> sqlExpr -> sqlFormula -> sqlStmt
  | sqlDeleteStmt : nat -> sqlFormula -> sqlStmt
  .

  Program Instance sqlStmtS : Setoid sqlStmt.
  
End SQLSyntax.

Section SQLExprInductionPrinciple.
  Variables (p : sqlExpr -> Prop) (Q : list sqlExpr -> Prop).

  Hypothesis
    (pval : forall val, p (sqlValExpr val))
    (pvar : forall var, p (sqlVarExpr var))
    (pcol : forall e, p e -> forall col, p (sqlColExpr e col))
    (papp0 : Q List.nil)
    (papp1 : forall e, p e -> forall l, Q l -> Q (e :: l))
    (papp : forall builtin l, Q l -> p (sqlAppExpr builtin l)).
  
    Fixpoint sqlExpr_ind_2 e : p e :=
    match e as x return p x with
      | sqlValExpr val => pval val
      | sqlVarExpr var => pvar var
      | sqlColExpr e col => pcol e (sqlExpr_ind_2 e) col
      | sqlAppExpr builtin l =>
        papp builtin l ((
               fix dep_fold_right (l' : list sqlExpr) : Q l' :=
                 match l' as x return Q x with
                   | List.nil => papp0
                   | e :: es => papp1 e (sqlExpr_ind_2 e) es (dep_fold_right es)
                 end
             ) l)
    end.
End SQLExprInductionPrinciple.

Section SQLSemanticsDefs.
  Definition row := lista sqlVal.
  Instance rowS : Setoid row := listaS sqlValS.
  Definition col := lista (maybe sqlVal).
  Instance colS : Setoid col := listaS (maybeS sqlValS).
  Instance sqlVal_Pointed : Pointed sqlVal :=
    {
      point := vNat 0
    }.
  
  Definition table := matrixp sqlVal.
  Instance tableS : Setoid table := matrixpS sqlValS.
  Definition database := list table. 
  Instance databaseS : Setoid database := listS tableS.

  Definition store := FMapNat.t sqlVal.


  Section Getters.

    Definition _cellGetter t ri ci := previewS @ (nthTraversal @ t ∘ matrixCellTraversal ri ci).

    Instance _cellGetter_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _cellGetter.
    Proof.
      solve_proper.
    Qed.

    Definition cellGetter := injF3 _cellGetter _.

    Existing Instance ConstMaybeFunctor.
    Existing Instance ConstMaybe_Applicative.

    Definition _rowGetter t (ri: nat) : databaseS ~> maybeS (rowS) := previewS @ (nthTraversal @ t ∘ matrixRowTraversal ri).

    Instance _rowGetter_Proper : Proper (equiv ==> equiv ==> equiv) _rowGetter.
    Proof.
      solve_proper.
    Qed.

    Definition rowGetter := injF2 _rowGetter _.

    Definition _colGetter t (ci: nat) : databaseS ~>  maybeS (colS) :=
      previewS @ (nthTraversal @ t ∘ matrixColLens @ ci). 

    Instance _colGetter_Proper : Proper (equiv ==> equiv ==> equiv) _colGetter.
    Proof.
      solve_proper.
    Qed.

    Definition colGetter := injF2 _colGetter _.

    Definition _rowsGetter t : databaseS ~> maybeS (listaS (maybeS (rowS))) := previewS @ (nthTraversal @ t ∘ matrixRowsLens).

    Instance _rowsGetter_Proper : Proper (equiv ==> equiv) _rowsGetter.
    Proof.
      solve_proper.
    Qed.

    Definition rowsGetter := injF _rowsGetter _.

    Definition _tableGetter t : databaseS ~> maybeS tableS := previewS @ (nthTraversal @ t).

    Instance _tableGetter_Proper : Proper (equiv ==> equiv) _tableGetter.
    Proof.
      solve_proper.
    Qed.

    Definition tableGetter := injF _tableGetter _.

    Definition _widthGetter t : databaseS ~> maybeS (natS) :=
      previewS @ (nthTraversal @ t ∘ matrixWidthLens).

    Instance _widthGetter_Proper : Proper (equiv ==> equiv) _widthGetter.
    Proof.
      solve_proper.
    Qed.

    Definition widthGetter := injF _widthGetter _.

   
    Definition tableRowsGetter : tableS ~> listaS (maybeS (rowS)) := view (matrixRowsLens).

    Definition tableWidthGetter : tableS ~>  (natS) :=
      view (matrixWidthLens).

    Definition _tableCellGetter ri ci : tableS ~> (maybeS sqlValS) :=
      previewS @ (matrixCellTraversal ri ci).

    Instance _tableCellGetter_Proper : Proper (equiv ==> equiv ==> equiv) _tableCellGetter.
    Proof.
      solve_proper.
    Qed.

    Definition tableCellGetter := injF2 _tableCellGetter  _.

    Definition rowColGetter n : rowS ~> sqlValS := view (listaNthLens n).



    Definition _maybeRowGetter (t: nat) (ri: nat) : databaseS ~>  maybeS (maybeS rowS) :=
      previewS @ (nthTraversal @ t ∘ matrixRowsLens ∘ listaNthLens ri). 

    Instance _maybeRowGetter_Proper : Proper (equiv ==> equiv ==> equiv) _maybeRowGetter.
    Proof.
      autounfold. intros. unfold _maybeRowGetter. rewritesr.
    Qed.

    Definition maybeRowGetter : natS ~> natS ~~> databaseS ~~> maybeS (maybeS rowS) := injF2 _maybeRowGetter _.




    Lemma tableWidthGetter_1 : forall n (l : lista (maybe (lista sqlVal))), tableWidthGetter @ (matrixpCons _ n l) = n.
    Proof.
      intros. reflexivity.
    Qed.
    


    Lemma widthGetter_0 : forall tab h, widthGetter @ 0 @ (tab :: h) = Some (tableWidthGetter @ tab).
    Proof.
      intros. simpl. auto.
    Qed.
    

    Section Comps.

      Lemma cellGetter_comp :
        forall t ri ci h,
          (tableGetter @ t @ h) >>= tableCellGetter @ ri @ ci == cellGetter @ t @ ri @ ci @ h.
      Proof.
        intros. unfold cellGetter. normalize. unfold _cellGetter. rewrite nthTraversal_comp_preview. reflexivity.
      Qed.
      
    End Comps.

  End Getters.
  
  Section Setters.
    Existing Instance ConstMaybeFunctor.
    Existing Instance ConstMaybe_Applicative.

    Existing Instance IdentityFunctor.
    Existing Instance Identity_Applicative.

    Definition _cellSetter t (ri: nat) (ci: nat) (n : sqlVal) : databaseS ~> databaseS :=
      setS @ (nthTraversal @ t ∘ matrixCellTraversal ri ci) @ n.

    Instance _cellSetter_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) _cellSetter.
    Proof.
      solve_proper.
    Qed.

    Definition cellSetter := injF4 _cellSetter _.
    
    Definition _rowSetter t (ri: nat) (r : row) : databaseS ~> databaseS :=
      setS @ (nthTraversal @ t ∘ matrixRowTraversal ri) @ r.

    Instance _rowSetter_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _rowSetter.
    Proof.
      autounfold. intros. unfold _rowSetter, set. rewritesr. 
    Qed.

    Definition rowSetter := injF3 _rowSetter _.
    
    Definition _maybeRowSetter (t: nat) (ri: nat) (r : maybe row) : databaseS ~>  databaseS :=
      setS @ (nthTraversal @ t ∘ matrixRowsLens ∘ listaNthLens ri) @ r. 

    Instance _maybeRowSetter_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _maybeRowSetter.
    Proof.
      autounfold. intros. unfold _maybeRowSetter, set. rewritesr.
    Qed.

    Definition maybeRowSetter := injF3 _maybeRowSetter _.

    Definition _rowsSetter (t: nat) (rows : lista (maybe row)) : databaseS ~>  databaseS :=
      setS @ (nthTraversal @ t ∘ matrixRowsLens) @ rows.

    Instance _rowsSetter_Proper : Proper (equiv ==> equiv ==> equiv) _rowsSetter.
    Proof.
      autounfold. intros. unfold _rowsSetter, set. rewritesr.
    Qed.

    Definition rowsSetter := injF2 _rowsSetter _.
     
  End Setters.
  
  Instance FMapNat_Equal_Equivalence A : Equivalence (@FMapNat.Equal A).
  Proof.
    split.
    autounfold. unfold FMapNat.Equal. intros. reflexivity.
    autounfold. unfold FMapNat.Equal. intros. symmetry. auto.
    autounfold. unfold FMapNat.Equal. intros. transitivity (FMapNat.find y0 y). auto. auto.
  Qed.
  
  Instance FMapNatSetoid A : Setoid (FMapNat.t A) :=
    {
      equiv := @FMapNat.Equal A
    }.
  

  Instance storeS : Setoid store := FMapNatSetoid sqlVal.  
  Definition colLookup val colind : option sqlVal :=
    match val with
      | vRow row =>     nth_error row colind
      | _ => None
    end
  .

  Definition storeProd (s1 s2 : store) : store :=
    FMapNat.fold (fun k e s => FMapNat.add k e s) s1 s2.
  
  Definition storesProd (ss1 ss2 : list store) : list store :=
    concat (map (fun s => map (fun s2 => storeProd s s2) ss2) ss1).

End SQLSemanticsDefs.

Opaque matrixCellTraversal matrixRowTraversal matrixWidthLens listaNthLens matrixColLens matrixRowsLens maybePrism.


Opaque rowsGetter rowsSetter maybeRowGetter maybeRowSetter rowGetter rowSetter cellGetter cellSetter widthGetter tableGetter tableWidthGetter tableRowsGetter tableCellGetter.

