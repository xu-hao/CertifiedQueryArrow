Require Import Assert Utils Command.
Require Import FMapWeakList List.
Require Import Coq.Structures.DecidableTypeEx.

Module FMapNat := FMapWeakList.Make Nat_as_DT.
Module NatNat_as_DT := PairDecidableType Nat_as_DT Nat_as_DT.
Module FMapNatNat := FMapWeakList.Make NatNat_as_DT.

Definition singleton {T} (k : nat) (v : T) : FMapNat.t T :=
  FMapNat.add k v (FMapNat.empty T).
  
Section SQLSyntax.
  Definition table := nat.
  Definition col := nat.
  Definition tableSchema := list col.

  Inductive sqlExpr :=
  | sqlValExpr : val -> sqlExpr
  | sqlAppExpr : builtin -> list sqlExpr -> sqlExpr
  | sqlColExpr : var -> pred -> sqlExpr
  .

  Inductive sqlFormula :=
  | sqlBuiltIn : builtin -> list sqlExpr -> sqlFormula
  | sqlAnd : sqlFormula -> sqlFormula -> sqlFormula
  | sqlOr : sqlFormula -> sqlFormula -> sqlFormula
  | sqlNot : sqlFormula -> sqlFormula
  | sqlExists : sql -> sqlFormula
  with
  sql :=
  | sqlQuery : list (sqlExpr * col) -> list (sqlTableExpr * var) -> sqlFormula -> sql
  with
  sqlTableExpr :=
  | sqlTable : table -> sqlTableExpr
  | sqlSelect : sql -> sqlTableExpr
  .

  Inductive sqlStmt :=
  | sqlQueryStmt : sql -> sqlStmt
  | sqlInsertStmt : table -> list col -> sql -> sqlStmt
  | sqlUpdateStmt : table -> col -> sqlExpr -> sqlFormula -> sqlStmt
  | sqlDeleteStmt : table -> sqlFormula -> sqlStmt
  .

End SQLSyntax.

Section SQLExprInductionPrinciple.
  Variables (p : sqlExpr -> Prop) (Q : list sqlExpr -> Prop).

  Hypothesis
    (pval : forall val, p (sqlValExpr val))
    (pvar : forall var col, p (sqlColExpr var col))
    (papp0 : Q List.nil)
    (papp1 : forall e, p e -> forall l, Q l -> Q (e :: l))
    (papp : forall builtin l, Q l -> p (sqlAppExpr builtin l)).
  
    Fixpoint sqlExpr_ind_2 e : p e :=
    match e as x return p x with
      | sqlValExpr val => pval val
      | sqlColExpr var col => pvar var col
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
  Definition row := FMapNat.t val.
  Definition resultSet := list row.
  Definition database := FMapNat.t resultSet.
  Definition store := FMapNat.t row.
  
  Definition storeLookup s var col : option val :=
    match FMapNat.find var s with
      | Some row => FMapNat.find col row
      | None => None
    end
  .
  
  Definition storeProd (s1 s2 : store) : store :=
    FMapNat.fold (fun k e s => FMapNat.add k e s) s1 s2.
  
  Definition storesProd (ss1 ss2 : list store) : list store :=
    concat (map (fun s => map (fun s2 => storeProd s s2) ss2) ss1).
End SQLSemanticsDefs.
Module SQLSemantics (B: BuiltInExpr) (BP : BuiltInPred).
    
    Fixpoint sqlExprEval (s : store) (e : sqlExpr) : option val :=
      match e with
        | sqlValExpr val => Some val
        | sqlColExpr var col =>
          storeLookup s var col
        | sqlAppExpr builtin args =>
          match sequence (map (sqlExprEval s) args) with
            | Some l => B.app builtin l
            | None => None
          end
      end
    .
    
    Fixpoint sqlFormEval (s : store) (m : database) (form: sqlFormula) : option bool :=
      match form with
        | sqlBuiltIn builtin args =>
          match sequence (map (sqlExprEval s) args) with
            | Some l => BP.app builtin l
            | None => None
          end
        | sqlAnd form1 form2 =>
          match sqlFormEval s m form1 with
            | Some b1 =>
              match sqlFormEval s m form2 with
                | Some b2 => Some (andb b1 b2)
                | None => None
              end
            | None => None
          end
        | sqlOr form1 form2 =>
          match sqlFormEval s m form1 with
            | Some b1 =>
              match sqlFormEval s m form2 with
                | Some b2 => Some (orb b1 b2)
                | None => None
              end
            | None => None
          end
        | sqlNot form1 =>
          match sqlFormEval s m form1 with
            | Some b1 => Some (negb b1)
            | None => None
          end
        | sqlExists sql =>
          match sqlReduce s m sql with
            | Some l => Some (null l)
            | None => None
          end
      end
    with
    sqlReduce (s : store) (m : database) (sql1 : sql) : option resultSet :=
      match sql1 with
        | sqlQuery rets tabs form =>
          match sequence (map (fun tab : sqlTableExpr * col =>
                                 let (te, var) := tab in
                                 match (sqlTableExprEval s m te) with
                                   | Some rs => Some (map (fun r => singleton var r) rs)
                                   | None => None
                                 end) tabs) with
            | Some l =>
              let ss := fold_left storesProd l (s :: List.nil) in
              match sequence (map (fun s =>
                                     match sqlFormEval s m form with
                                       | Some b => if b then Some (s::List.nil) else Some List.nil 
                                       | _ => None
                                     end) ss) with
                | Some ss' =>
                  let filtered := concat ss' in
                  sequence (map (fun s =>
                                   fold_left (fun rs (ret : sqlExpr * var) =>
                                                match rs with
                                                  | Some rs' =>
                                                    let (e, c) := ret in
                                                    match sqlExprEval s e with
                                                      | Some val => Some (FMapNat.add c val rs')
                                                      | None => None
                                                    end
                                                  | None => None
                                                end
                                             ) rets (Some (FMapNat.empty val))) filtered)
                | None => None
              end
            | None => None
          end
      end
    with
    sqlTableExprEval (s : store) (m : database) (te : sqlTableExpr) : option resultSet :=
      match te with
        | sqlTable tab => FMapNat.find tab m
        | sqlSelect sql1 => sqlReduce s m sql1
      end
    .
    
End SQLSemantics.

Module SQLStore <: Store.
  Definition t := store.
  Definition read (s : store) (v : var) : option val :=
    match FMapNat.find v s with
      | Some r => FMapNat.find 0 r
      | None => None
    end.
  Definition update (s : store) (v : var) (val1 : val) : store :=
    FMapNat.add v (singleton 0 val1) s.
  Definition delete (s : store) (v : var) : store :=
    FMapNat.remove v s.
  Definition empty : store := FMapNat.empty row.
  Definition dom (s : store) : FVarSet.t :=
    fold_right (fun e s => ﹛e﹜∪ s) ∅ (map fst (FMapNat.elements s)).

  Lemma read_update :
    forall s var val,
      read (update s var val) var = Some val.
  Proof.
    intros. unfold update. unfold read.
    rewrite FMapNat.find_1 with (e:=singleton 0 val).
    unfold singleton.
    rewrite FMapNat.find_1 with (e:=val).
    auto.
    apply FMapNat.add_1.
    auto.
    apply FMapNat.add_1.
    auto.
  Qed.

  Lemma delete_update :
    forall s var val,
      delete (update s var val) var = delete s var.
  Proof.
    intros. unfold update. unfold delete. unfold FMapNat.Equal. simpl.
  Proof.
  Lemma update_delete :
    forall s var val,
       (delete s var) [ var ↦ val ]s = s [ var ↦ val ]s.
  
  Lemma update_update :
    forall s var var2 val val2,
      s [ var ↦ val ]s [ var2 ↦ val2 ]s = s [ var2 ↦ val2 ]s.
  
  Lemma read_update_diff_var :
    forall s var var2 val,
      s [ var ↦ val ]s [ var2 ]s = s [ var2 ]s.

  Lemma update_update_diff_var :
    forall s var var2 val val2,
      s [ var ↦ val ]s [ var2 ↦ val2 ]s = s [ var2 ↦ val2 ]s [ var ↦ val ]s.

  Lemma delete_update_diff_var:
    forall s var var2 val,
      delete (s [ var ↦ val ]s) var2 = (delete s var2) [ var ↦ val ]s.

  Lemma read_delete_diff_var :
    forall s var var2,
      (delete s var) [var2]s = s[var2]s.
  Lemma read_delete :
    forall s var,
      (delete s var) [var]s = None.

End SQLStore.
