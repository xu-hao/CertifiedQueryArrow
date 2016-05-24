Require Import Definitions Algebra.Monoid  Algebra.SetoidCat Algebra.Maybe Tactics Algebra.ListUtils Algebra.Functor Algebra.Applicative Algebra.Alternative Algebra.FoldableFunctor Algebra.PairUtils Algebra.Maybe Algebra.Monad Algebra.Lens.Lens ListLens MaybeLens Utils SetoidUtils MonoidUtils Pointed Lista Matrixp ListaLens MatrixpLens GenUtils.
Require Import Coq.Structures.DecidableTypeEx List  SetoidClass PeanoNat FMapWeakList Basics Coq.Init.Specif.

Module FMapNat := FMapWeakList.Make Nat_as_DT.
Module NatNat_as_DT := PairDecidableType Nat_as_DT Nat_as_DT.
Module FMapNatNat := FMapWeakList.Make NatNat_as_DT.

Definition singleton {T} (k : nat) (v : T) : FMapNat.t T :=
  FMapNat.add k v (FMapNat.empty T).

Open Scope type_scope.
Definition sqlPred := nat (* table index *) * nat (* col index *).

Instance sqlPredS : Setoid sqlPred := natS ~*~ natS.

Definition sqlType := nat (* table index *).

Instance sqlTypeS : Setoid sqlType := natS.

Definition sqlAddr := nat (* table index *) * nat (* row index *).

Instance sqlAddrS : Setoid sqlAddr := natS ~*~ natS.

Inductive sqlVal :=
| vNat : nat -> sqlVal
| vAddr : sqlAddr -> sqlVal
.

Program Instance sqlValS : Setoid sqlVal.

Module SQLValType <: ValType.
  Definition val := sqlVal.

  Instance valS : Setoid sqlVal := sqlValS.

  Fixpoint equiv_dec val1 val2 : {val1 == val2} + {~ val1 == val2}.
  Proof.
    destruct val1, val2.
    destruct (Nat.eq_dec n n0). left. congruence.
    right. congruence.
    right. intro. inversion H.
    right. intro. inversion H.
    destruct s as [n n0], s0 as [n1 n2].
    destruct (Nat.eq_dec n n1), (Nat.eq_dec n0 n2). left. congruence.
    right. intro. inversion H. tauto.
    right. intro. inversion H. tauto.
    right. intro. inversion H. tauto.
  Qed.
End SQLValType.

Section SQLSyntax.
  
  Context
    (sqlBuiltInExprT : Type)
    (sqlBuiltInFormulaT : Type).


  Inductive sqlExpr :=
  | sqlValExpr : sqlVal -> sqlExpr
  | sqlVarExpr : var -> sqlExpr
  | sqlAppExpr : sqlBuiltInExprT -> list sqlExpr -> sqlExpr
  | sqlColExpr : sqlExpr -> nat (* col index *) -> sqlExpr
  .

  Program Instance sqlExprS : Setoid sqlExpr. 

  Inductive sqlFormula :=
  | sqlBuiltInFormula : sqlBuiltInFormulaT -> list sqlExpr -> sqlFormula
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
  Program Instance sqlS : Setoid sql.
  Program Instance sqlTableExprS : Setoid sqlTableExpr.
  
  Inductive sqlStmt :=
  | sqlQueryStmt : sql -> sqlStmt
  | sqlInsertStmt : nat (* table index *) -> sql -> sqlStmt
  | sqlUpdateStmt : nat -> nat (* col index *) -> sqlExpr -> sqlFormula -> sqlStmt
  | sqlDeleteStmt : nat -> sqlFormula -> sqlStmt
  .

  Program Instance sqlStmtS : Setoid sqlStmt.
  

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

Section SQLFormulaDoubleInductionPrinciple.
  Variables
    (p : sqlFormula -> sqlFormula -> Prop)
    (q : sql -> sql -> Prop)
    (u : list (sqlTableExpr * var) -> list (sqlTableExpr * var) -> Prop)
    (v : sqlTableExpr -> sqlTableExpr -> Prop)    
  .

  Hypothesis
    (pbibi : forall bi args bi2 args2, p (sqlBuiltInFormula bi args) (sqlBuiltInFormula bi2 args2))
    (pbiand : forall bi args a b, p (sqlBuiltInFormula bi args) (sqlAnd a b))
    (pbior : forall bi args a b, p (sqlBuiltInFormula bi args) (sqlOr a b))
    (pbinot : forall bi args a, p (sqlBuiltInFormula bi args) (sqlNot a))
    (pbiexi : forall bi args s, p (sqlBuiltInFormula bi args) (sqlExists s))
    (pandbi : forall x y bi2 args2, p (sqlAnd x y) (sqlBuiltInFormula bi2 args2))
    (pandand : forall x y a b, p x a -> p y b -> p (sqlAnd x y) (sqlAnd a b))
    (pandor : forall x y a b, p (sqlAnd x y) (sqlOr a b))
    (pandnot : forall x y a, p (sqlAnd x y) (sqlNot a))
    (pandexi : forall x y s, p (sqlAnd x y)  (sqlExists s))
    (porbi : forall x y bi2 args2, p (sqlOr x y) (sqlBuiltInFormula bi2 args2))
    (porand : forall x y a b, p (sqlOr x y) (sqlAnd a b))
    (poror : forall x y a b, p x a -> p y b -> p (sqlOr x y) (sqlOr a b))
    (pornot : forall x y a, p (sqlOr x y) (sqlNot a))
    (porexi : forall x y s, p (sqlOr x y)  (sqlExists s))
    (pnotbi : forall x bi2 args2, p (sqlNot x) (sqlBuiltInFormula bi2 args2))
    (pnotand : forall x a b, p (sqlNot x) (sqlAnd a b))
    (pnotor : forall x a b, p (sqlNot x) (sqlOr a b))
    (pnotnot : forall x a, p x a -> p (sqlNot x) (sqlNot a))
    (pnotexi : forall x s, p (sqlNot x)  (sqlExists s))
    (pexibi : forall r bi2 args2, p (sqlExists r) (sqlBuiltInFormula bi2 args2))
    (pexiand : forall r a b, p (sqlExists r) (sqlAnd a b))
    (pexior : forall r a b, p (sqlExists r) (sqlOr a b))
    (pexinot : forall r a, p (sqlExists r) (sqlNot a))
    (pexiexi : forall r s, q r s -> p (sqlExists r)  (sqlExists s))
    (qqueque : forall es1 es2 tel1 tel2 a b, u tel1 tel2 -> p a b -> q (sqlQuery es1 tel1 a) (sqlQuery es2 tel2 b))
    (vtabtab : forall t1 t2, v (sqlTable t1) (sqlTable t2))
    (vtabsel : forall t1 q2, v (sqlTable t1) (sqlSelect q2))
    (vseltab : forall q1 t2, v (sqlSelect q1) (sqlTable t2))
    (vselsel : forall q1 q2, q q1 q2 -> v (sqlSelect q1) (sqlSelect q2))
    (unilnil : u nil nil)
    (unilcons : forall te tel, u nil tel -> u nil (te :: tel))
    (uconsnil : forall te tel, u tel nil -> u (te :: tel) nil)
    (uconscons : forall te1 v1 tel1 te2 v2 tel2, v te1 te2 -> u tel1 tel2 -> u ((te1, v1) :: tel1) ((te2, v2) :: tel2))
  .
  
    Fixpoint sqlFormula_ind_2 f1 f2 : p f1 f2 :=
      match f1 in sqlFormula return p f1 f2 with
        | sqlBuiltInFormula bi args =>
          match f2  in sqlFormula return p (sqlBuiltInFormula bi args) f2 with
            | sqlBuiltInFormula bi2 args2 => pbibi bi args bi2 args2
            | sqlAnd a b => pbiand bi args a b
            | sqlOr a b => pbior bi args a b
            | sqlNot a => pbinot bi args a 
            | sqlExists s => pbiexi bi args s
          end
        | sqlAnd x y =>
          match f2 in sqlFormula return p (sqlAnd x y) f2 with
            | sqlBuiltInFormula bi2 args2 => pandbi x y bi2 args2
            | sqlAnd a b => pandand x y a b (sqlFormula_ind_2 x a) (sqlFormula_ind_2 y b)
            | sqlOr a b => pandor x y a b
            | sqlNot a => pandnot x y a 
            | sqlExists s => pandexi x y s
          end
        | sqlOr x y =>
          match f2 in sqlFormula return p (sqlOr x y) f2 with
            | sqlBuiltInFormula bi2 args2 => porbi x y bi2 args2
            | sqlAnd a b => porand x y a b
            | sqlOr a b => poror x y a b (sqlFormula_ind_2 x a) (sqlFormula_ind_2 y b)
            | sqlNot a => pornot x y a 
            | sqlExists s => porexi x y s
          end
        | sqlNot x =>
          match f2 in sqlFormula return p (sqlNot x) f2 with
            | sqlBuiltInFormula bi2 args2 => pnotbi x bi2 args2
            | sqlAnd a b => pnotand x a b
            | sqlOr a b => pnotor x a b
            | sqlNot a => pnotnot x a (sqlFormula_ind_2 x a) 
            | sqlExists s => pnotexi x s
          end
        | sqlExists r =>
          match f2 in sqlFormula return p (sqlExists r) f2 with
            | sqlBuiltInFormula bi2 args2 => pexibi r bi2 args2
            | sqlAnd a b => pexiand r a b
            | sqlOr a b => pexior r a b
            | sqlNot a => pexinot r a 
            | sqlExists s =>
              pexiexi r s ((fix h' (q1 q2 : sql) : q q1 q2 :=
                              match q1 in sql, q2 in sql return q q1 q2 with
                                | sqlQuery es1 tel1 a, sqlQuery es2 tel2 b =>
                                  qqueque es1 es2 tel1 tel2 a b
                                          ((fix h'' (c d : list(sqlTableExpr * var)) : u c d :=
                                              match c in list _ return u c d with
                                                | nil =>
                                                  (fix h''' (d' : list(sqlTableExpr * var)) : u nil d' :=
                                                     match d' in list _ return u nil d' with
                                                       | nil => unilnil
                                                       | d' :: ds' => unilcons d' ds' (h''' ds')
                                                     end) d
                                                | (te, v1) :: cs' =>
                                                  (fix h''' (d' : list(sqlTableExpr * var)) :=
                                                     match d in list _ return u ((te, v1)::cs') d with
                                                       | nil => uconsnil (te,v1) cs' (h'' cs' nil)
                                                       | (te2, v2) :: ds' =>
                                                         uconscons te v1 cs' te2 v2 ds' (
                                                                     match te in sqlTableExpr, te2 in sqlTableExpr return v te te2 with
                                                                       | sqlTable n1, sqlTable n2 => vtabtab n1 n2
                                                                       | sqlTable n1, sqlSelect q2 => vtabsel n1 q2
                                                                       | sqlSelect q1, sqlTable n2 => vseltab q1 n2
                                                                       | sqlSelect q1, sqlSelect q2 => vselsel q1 q2 (h' q1 q2)
                                                                     end
                                                                   ) (h'' cs' ds')
                                                     end) d
                                              end
                                           ) tel1 tel2)
                                          (sqlFormula_ind_2 a b)
                              end) r s)
          end
    end.

End SQLFormulaDoubleInductionPrinciple.
End SQLSyntax.

Section SQLSemanticsDefs.
  Instance sqlVal_Pointed : Pointed sqlVal :=
    {
      point := vNat 0
    }.
  
  Definition row := lista sqlVal.
  Instance rowS : Setoid row := listaS sqlValS.
  Definition col := lista (maybe sqlVal).
  Instance colS : Setoid col := listaS (maybeS sqlValS).
  
  Definition table := matrixp sqlVal.
  Instance tableS : Setoid table := matrixpS sqlValS.
  Definition database := list table. 
  Instance databaseS : Setoid database := listS tableS.

  Definition store := lista (maybe sqlVal).


  Section Getters.

    Existing Instance ComposeP_Preview.
    Definition _cellGetter (t ri ci : nat) : databaseS ~> maybeS sqlValS := preview @ (nthPreview t >>>? matrixCellPreview ri ci).

    Instance _cellGetter_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _cellGetter.
    Proof.
      solve_proper.
    Qed.

    Definition cellGetter := injF3 _cellGetter _.

    Definition _rowGetter (t ri: nat) : databaseS ~> maybeS (rowS) := preview @ (nthPreview t >>>? matrixRowsLens >>>? listaNthLens ri >>>? maybePreview).

    Instance _rowGetter_Proper : Proper (equiv ==> equiv ==> equiv) _rowGetter.
    Proof.
      solve_proper.
    Qed.

    Definition rowGetter := injF2 _rowGetter _.

    Definition _colGetter (t ci: nat) : databaseS ~>  maybeS (colS) :=
      (caseMaybeS
        @ (SomeS ∘ readMatrixCol @ ci)
        @ None)
        ∘ (preview @ (nthPreview t)).

    Instance _colGetter_Proper : Proper (equiv ==> equiv ==> equiv) _colGetter.
    Proof.
      solve_proper.
    Qed.

    Definition colGetter := injF2 _colGetter _.

    Definition _rowsGetter t : databaseS ~> maybeS (listaS (maybeS (rowS))) :=
      preview @ (nthPreview t >>>? matrixRowsLens).

    Instance _rowsGetter_Proper : Proper (equiv ==> equiv) _rowsGetter.
    Proof.
      solve_proper.
    Qed.

    Definition rowsGetter := injF _rowsGetter _.

    Definition _tableGetter t : databaseS ~> maybeS tableS := preview @ (nthPreview t).

    Instance _tableGetter_Proper : Proper (equiv ==> equiv) _tableGetter.
    Proof.
      solve_proper.
    Qed.

    Definition tableGetter := injF _tableGetter _.

    (*Definition _widthGetter t : databaseS ~> maybeS (natS) :=
      (caseMaybeS
        @ (SomeS ∘ width)
        @ None)
        ∘ (preview @ (nthPreview t)).

    Instance _widthGetter_Proper : Proper (equiv ==> equiv) _widthGetter.
    Proof.
      solve_proper.
    Qed.

    Definition widthGetter := injF _widthGetter _.*)

   
    Definition tableRowsGetter : tableS ~> listaS (maybeS (rowS)) := view @ (matrixRowsLens).

    Definition tableColGetter : natS ~> tableS ~~> listaS (optionS sqlValS) := readMatrixCol.

(*    Definition tableWidthGetter : tableS ~>  (natS) :=
      view (matrixWidthLens).*)

    Definition _tableCellGetter ri ci : tableS ~> (maybeS sqlValS) :=
      preview @ (matrixCellPreview ri ci).

    Instance _tableCellGetter_Proper : Proper (equiv ==> equiv ==> equiv) _tableCellGetter.
    Proof.
      solve_proper.
    Qed.

    Definition tableCellGetter := injF2 _tableCellGetter  _.

    Definition rowColGetter n : rowS ~> sqlValS := view @ (listaNthLens n).



    Definition _maybeRowGetter (t: nat) (ri: nat) : databaseS ~>  maybeS (maybeS rowS) :=
      preview @ (nthPreview t >>>? matrixRowsLens >>>? listaNthLens ri). 

    Instance _maybeRowGetter_Proper : Proper (equiv ==> equiv ==> equiv) _maybeRowGetter.
    Proof.
      autounfold. intros. unfold _maybeRowGetter. rewritesr.
    Qed.

    Definition maybeRowGetter : natS ~> natS ~~> databaseS ~~> maybeS (maybeS rowS) := injF2 _maybeRowGetter _.




(*    Lemma tableWidthGetter_1 : forall n (l : lista (maybe (lista sqlVal))), tableWidthGetter @ (matrixpCons _ n l) = n.
    Proof.
      intros. reflexivity.
    Qed.
    


    Lemma widthGetter_0 : forall tab h, widthGetter @ 0 @ (tab :: h) = Some (tableWidthGetter @ tab).
    Proof.
      intros. simpl. auto.
    Qed.*)
    

(*    Section Comps.

      Lemma cellGetter_comp :
        forall t ri ci h,
          (tableGetter @ t @ h) >>= tableCellGetter @ ri @ ci == cellGetter @ t @ ri @ ci @ h.
      Proof.
        intros. unfold cellGetter. normalize. unfold _cellGetter. rewrite nthTraversal_comp_preview. reflexivity.
      Qed.
      
    End Comps.*)

  End Getters.
  
  Section Setters.

    Existing Instance ComposeP_Preview.
    Definition _cellSetter t (ri: nat) (ci: nat) (n : sqlVal) : databaseS ~> databaseS :=
      set @ (nthPreview t >>>? matrixCellPreview ri ci) @ n.

    Instance _cellSetter_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) _cellSetter.
    Proof.
      solve_proper.
    Qed.

    Definition cellSetter := injF4 _cellSetter _.
    

    Definition _rowSetter (t ri: nat) (r : row) : databaseS ~> databaseS :=
      set @ (nthPreview t >>>? matrixRowPreview ri) @ r.

    Instance _rowSetter_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _rowSetter.
    Proof.
      autounfold. intros. unfold _rowSetter, set. rewritesr. 
    Qed.

    Definition rowSetter := injF3 _rowSetter _.
    
    Definition _maybeRowSetter (t: nat) (ri: nat) (r : maybe row) : databaseS ~>  databaseS :=
      set @ (nthPreview t >>>? matrixMaybeRowLens ri) @ r. 

    Instance _maybeRowSetter_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _maybeRowSetter.
    Proof.
      autounfold. intros. unfold _maybeRowSetter, set. rewritesr.
    Qed.

    Definition maybeRowSetter := injF3 _maybeRowSetter _.

    Definition _rowsSetter (t: nat) (rows : lista (maybe row)) : databaseS ~>  databaseS :=
      set @ (nthPreview t >>>? matrixRowsLens ) @ rows.

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
  
  Instance storeS : Setoid store := listaS (maybeS sqlValS).  
  Definition colLookup row colind : option sqlVal :=
    nth_error row colind.

  Existing Instance maybe_first_Monoid.
  Definition storeProd (s1 s2 : store) : store :=
    lista_zipWith mappend s2 s1.
  
  Definition storesProd (ss1 ss2 : list store) : list store :=
    concat (map (fun s => map (fun s2 => storeProd s s2) ss2) ss1).

End SQLSemanticsDefs
.