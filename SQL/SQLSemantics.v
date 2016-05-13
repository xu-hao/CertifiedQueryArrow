Require Import Assert Command Definitions Algebra.Monoid Expr Algebra.SetoidCat Algebra.Maybe Tactics Algebra.ListUtils Algebra.Functor Algebra.Applicative Algebra.Alternative Algebra.FoldableFunctor Algebra.PairUtils Algebra.Maybe Algebra.Monad Algebra.Lens Utils SetoidUtils SQLStore SQLHeap.
Require Import Coq.Structures.DecidableTypeEx List SetoidClass PeanoNat FMapWeakList Basics.

Module SQLBuiltInExpr <: BuiltInExpr SQLValType.
  Definition builtInExpr := sqlBuiltIn.
  Definition builtInExprS := natS.
  Definition appBIE : builtInExprS ~> listS SQLValType.valS ~~> optionS SQLValType.valS :=
    constS _ @ (constS _ @ None).
End SQLBuiltInExpr.

Module SQLBuiltInFormula <: BuiltInFormula SQLValType SQLStore SQLHeap.
  Definition builtInFormula := sqlFormula.
  Instance builtInFormulaS : Setoid builtInFormula := sqlFormulaS.
  Definition appBIE : sqlFormulaS ~> listS sqlValS ~~> databaseS ~~> storeS ~~> listS storeS :=
  constS _ @ (constS _ @ (constS _ @ constS _ @ nil)).
End SQLBuiltInFormula.
      
Module SQLModel .
  (* SQL as builtInFormula and builtInCommand *)
  Fixpoint sqlExprEval (s : store) (e : sqlExpr) : option sqlVal :=
    match e with
      | sqlValExpr val => Some val
      | sqlVarExpr var => FMapNat.find var s
      | sqlColExpr e colind =>
        match sqlExprEval s e with
          | Some val =>
            match colLookup val colind with
              | Some n => Some (vNat n)
              | None => None
            end
          | None => None
        end
      | sqlAppExpr builtin args =>
        match sequence (map (sqlExprEval s) args) with
          | Some l => SQLBuiltInExpr.appBIE @ builtin @ l
          | None => None
        end
    end
  .


    Fixpoint sqlFormEval (s : store) (m : database) (form: sqlFormula) : option bool :=
      match form with
        | sqlBuiltIn builtin args =>
          match sequence (map (sqlExprEval s) args) with
            | Some l => BP.app @ builtin @ l
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
          match sequence (map (fun tab : sqlTableExpr * var =>
                                 let (te, var) := tab in
                                 match (sqlTableExprEval s m te) with
                                   | Some rs => Some (map (fun r => singleton var (vRow r)) rs)
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
                                   sequence (map (fun (e : sqlExpr) =>
                                                    match sqlExprEval s e with
                                                      | Some val =>
                                                        match val with
                                                          | vNat nat => Some nat
                                                          | _ => None
                                                        end     
                                                      | None => None
                                                    end
                                             ) rets) ) filtered)
                | None => None
              end
            | None => None
          end
      end
    with
    sqlTableExprEval (s : store) (m : database) (te : sqlTableExpr) : option resultSet :=
      match te with
        | sqlTable tab => match (nth_error m tab) with
                            | Some tab => Some (snd tab)
                            | None => None
                          end
        | sqlSelect sql1 => sqlReduce s m sql1
      end
    .
    
End SQLModel.
