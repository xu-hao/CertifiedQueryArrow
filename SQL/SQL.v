Require Import Assert Command Definitions Algebra.Monoid Expr Algebra.SetoidCat Algebra.Maybe Tactics Algebra.ListUtils Algebra.Functor Algebra.Applicative Algebra.Alternative Algebra.FoldableFunctor Algebra.PairUtils Algebra.Maybe Algebra.Monad Algebra.Lens.Lens ListLens Utils SetoidUtils MonoidUtils Pointed.
Require Import Coq.Structures.DecidableTypeEx List  SetoidClass PeanoNat FMapWeakList Basics Coq.Init.Specif.

Module FMapNat := FMapWeakList.Make Nat_as_DT.
Module NatNat_as_DT := PairDecidableType Nat_as_DT Nat_as_DT.
Module FMapNatNat := FMapWeakList.Make NatNat_as_DT.

Definition singleton {T} (k : nat) (v : T) : FMapNat.t T :=
  FMapNat.add k v (FMapNat.empty T).


Inductive sqlVal :=
| vNat : nat -> sqlVal
| vRow : list nat -> sqlVal
.

Program Instance sqlValS : Setoid sqlVal.

Module SQLValType <: ValType.
  Definition val := sqlVal.
  Instance valS : Setoid sqlVal :=
    {
      equiv := eq
    }.
  Lemma equiv_dec : forall val1 val2, {val1 == val2} + {~ val1 == val2}.
  Proof.
    intros. simpl. destruct val1, val2. destruct (Nat.eq_dec n n0). left. congruence.
    right. congruence.
    right. intro. inversion H.
    right. intro. inversion H.
    destruct (list_eq_dec Nat.eq_dec l l0).
    left. congruence.
    right. congruence.
  Qed.
End SQLValType.

Definition table := nat.
Instance tableS : Setoid nat := natS.
Definition colind := nat.
Definition coltype := nat.
Definition tableSchema := list coltype.
Definition sqlBuiltIn := nat.


Section SQLSyntax.
  

  Inductive sqlExpr :=
  | sqlValExpr : sqlVal -> sqlExpr
  | sqlVarExpr : var -> sqlExpr
  | sqlAppExpr : sqlBuiltIn -> list sqlExpr -> sqlExpr
  | sqlColExpr : sqlExpr -> colind -> sqlExpr
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
  | sqlTable : table -> sqlTableExpr
  | sqlSelect : sql -> sqlTableExpr
  .

  Program Instance sqlFormulaS : Setoid sqlFormula.
  
  Inductive sqlStmt :=
  | sqlQueryStmt : sql -> sqlStmt
  | sqlInsertStmt : table -> sql -> sqlStmt
  | sqlUpdateStmt : table -> colind -> sqlExpr -> sqlFormula -> sqlStmt
  | sqlDeleteStmt : table -> sqlFormula -> sqlStmt
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
  Definition row := lista nat.
  Instance rowS : Setoid row := listaS natS.
  Definition col := lista (maybe nat).
  Instance colS : Setoid col := listaS (maybeS natS).
  Definition rowind := nat.
  Definition database := list (matrixp nat). 
  Instance databaseS : Setoid database := listS (matrixpS natS).
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

    Definition _rowGetter t (ri: rowind) : databaseS ~> maybeS (rowS) := previewS @ (nthTraversal @ t ∘ matrixRowTraversal ri).

    Instance _rowGetter_Proper : Proper (equiv ==> equiv ==> equiv) _rowGetter.
    Proof.
      solve_proper.
    Qed.

    Definition rowGetter := injF2 _rowGetter _.

    Definition _colGetter t (ci: colind) : databaseS ~>  maybeS (colS) :=
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

    Definition _tableGetter t : databaseS ~> maybeS (matrixpS natS) := previewS @ (nthTraversal @ t).

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

    Definition tableRowsGetter : matrixpS natS ~> listaS (maybeS (rowS)) := view (matrixRowsLens).

    Definition tableWidthGetter : matrixpS natS ~>  (natS) :=
      view (matrixWidthLens).

    Definition tableCellGetter ri ci : matrixpS natS ~> (maybeS natS) :=
      previewS @ (matrixCellTraversal ri ci).
    
    Lemma ConstIso_iso : forall A B (AS : Setoid A) (BS : Setoid B) (a : B),
            match ConstIsoS BS AS @ a with
              | ConstIso _ _ a' => a'
            end = a.
    Proof.
      auto.
    Qed.

    Lemma ConstIso'_iso : forall A B (AS : Setoid A) (BS : Setoid B) a,
            ConstIso B A (ConstIso' B A a) = a.
    Proof.
      intros. destruct a. auto. 
    Qed.

    Definition _maybeRowGetter (t: table) (ri: rowind) : databaseS ~>  maybeS (maybeS rowS) :=
      previewS @ (nthTraversal @ t ∘ matrixRowsLens ∘ listaNthLens ri). 

    Instance _maybeRowGetter_Proper : Proper (equiv ==> equiv ==> equiv) _maybeRowGetter.
    Proof.
      autounfold. intros. unfold _maybeRowGetter. rewritesr.
    Qed.

    Definition maybeRowGetter := injF2 _maybeRowGetter _.

    Section CellGetter_comp.
      Opaque matrixCellTraversal.
    Lemma cellGetter_comp :
      forall t ri ci h,
        (tableGetter @ t @ h) >>= tableCellGetter ri ci = cellGetter @ t @ ri @ ci @ h.
    Proof.
      intros. generalize t h. clear t h. double induction t h.
      - reflexivity.
      - intros. Opaque equiv pre0. simpl. unfold _maybe_first_mappend. Transparent pre0. unfold pre0 at 1 2. Opaque pre0. simpl.
        match goal with
          | |- ?a = match ?b with _ => _ end => let H:=fresh "H" in assert (a = b) as H; [auto | rewrite H; destruct b; [reflexivity | reflexivity ] ] 
        end
          .
      - intros. simpl. reflexivity.
      - intros. Opaque equiv pre0. simpl in *. unfold _nthTraversal, _nthTraversal' in *. simpl in *. rewrite ConstIso'_iso. rewrite ConstIso'_iso. apply H0. 
    Qed.

    End CellGetter_comp.

  End Getters.
  
  Section Setters.
    Existing Instance ConstMaybeFunctor.
    Existing Instance ConstMaybe_Applicative.

    Existing Instance IdentityFunctor.
    Existing Instance Identity_Applicative.

    Definition _cellSetter t (ri: rowind) (ci: colind) (n : nat) : databaseS ~> databaseS :=
      setS @ (nthTraversal @ t ∘ matrixCellTraversal ri ci) @ n.

    Instance _cellSetter_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) _cellSetter.
    Proof.
      solve_proper.
    Qed.

    Definition cellSetter := injF4 _cellSetter _.
    
    Definition _rowSetter t (ri: rowind) (r : row) : databaseS ~> databaseS :=
      setS @ (nthTraversal @ t ∘ matrixRowTraversal ri) @ r.

    Instance _rowSetter_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _rowSetter.
    Proof.
      autounfold. intros. unfold _rowSetter, set. rewritesr. 
    Qed.

    Definition rowSetter := injF3 _rowSetter _.
    
    Definition _maybeRowSetter (t: table) (ri: rowind) (r : maybe row) : databaseS ~>  databaseS :=
      setS @ (nthTraversal @ t ∘ matrixRowsLens ∘ listaNthLens ri) @ r. 

    Instance _maybeRowSetter_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _maybeRowSetter.
    Proof.
      autounfold. intros. unfold _maybeRowSetter, set. rewritesr.
    Qed.

    Definition maybeRowSetter := injF3 _maybeRowSetter _.

    Definition _rowsSetter (t: table) (rows : lista (maybe row)) : databaseS ~>  databaseS :=
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
  Definition colLookup val colind : option nat :=
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

