Require Import FSetInterface.
Require Import Tactics  Algebra.SetoidCat  Algebra.Monad Algebra.SetoidCat.PairUtils Algebra.SetoidCat.MaybeUtils Algebra.Monad.Maybe Algebra.Alternative Algebra.Functor Algebra.FoldableFunctor Algebra.Applicative Algebra.Monoid Algebra.SetoidCat.NatUtils Algebra.SetoidCat.BoolUtils Algebra.Monoid.PropUtils QAL.Definitions Algebra.SetoidCat.ListUtils Algebra.SetoidCat.UnitUtils.

Require Import FMapWeakList  RelationClasses Relation_Definitions Morphisms SetoidClass.

Inductive argument val :=
| argumentVal : val -> argument val
| argumentVar : var -> argument val
.

Definition argument_equiv val (valS : Setoid val) : relation (argument val) :=
  fun a b => match a, b with
               | argumentVal _ va, argumentVal _ vb => va == vb
               | argumentVar _ va, argumentVar _ vb => va = vb
               | _, _ => False
             end
.

                                                           
Instance argument_Equivalence val (valS : Setoid val) : Equivalence (argument_equiv val valS).
Proof.
  split.
  - unfold Reflexive. intros. destruct x.
    + simpl. reflexivity.
    + simpl. auto.
  - unfold Symmetric. intros. destruct x, y.        
    + simpl in *. rewritesr.
    + simpl in *. auto.
    + simpl in *. auto.
    + simpl in *. auto.
  - unfold Transitive. intros. destruct x, y, z.
    + simpl in *. rewritesr.
    + simpl in *. auto.
    + simpl in *. tauto. 
    + simpl in *. auto.
    + simpl in *. auto.
    + simpl in *. tauto.
    + simpl in *. auto.
    + simpl in *. congruence.
Qed.

Program Instance argumentS val (valS : Setoid val) : Setoid (argument val).

Module Type AbstractHeap (PT : PredType) (VT : ValType).
  Parameter t : Type.
  Parameter tS : Setoid t.
  Parameter l : forall A, (Setoid A) -> Type.
  Parameter lS : forall A (AS : Setoid A), Setoid (l A AS).
  Parameter l_Alternative : @Alternative l lS.
  Parameter l_Functor : @Functor l lS.
  Parameter l_Foldable : @FoldableFunctor l lS l_Functor.
  Parameter l_Applicative : @Applicative l lS l_Functor.

  Parameter isEmpty : tS ~> iff_setoid.
  Parameter disjoint : tS ~> tS ~~> iff_setoid.
  Parameter union : tS ~> tS ~~> tS.
  Parameter lookup : PT.predS ~> listS (argumentS _ VT.valS) ~~> tS ~~> lS _ (listS (varS ~*~ VT.valS)).
  Parameter insert : PT.predS ~> listS VT.valS ~~> tS ~~> maybeS tS.
  Parameter delete : PT.predS ~> listS VT.valS ~~> tS ~~> maybeS tS.
  Parameter insertProp : PT.predS ~> listS VT.valS ~~> listS VT.valS ~~> tS ~~> maybeS tS.
  Parameter deleteProp : PT.predS ~> listS VT.valS ~~> listS VT.valS ~~> tS ~~> maybeS tS.

  Notation "a ⊥ b" := (disjoint @ a @ b) (at level 15). 
  Notation "a ⋅ b" := (union @ a @ b) (at level 15). 
End AbstractHeap.  

