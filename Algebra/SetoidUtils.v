Require Import Utils Tactics SetoidCat.

Require Import List RelationClasses Relation_Definitions Morphisms Coq.Program.Basics SetoidClass.


Program Instance natS : Setoid nat.
Program Instance boolS : Setoid bool.



  Instance equiv_equiv_Proper {A} {R : relation A} (Eq: Equivalence R) : Proper (R ==> R ==> iff) R.
  Proof.
    unfold Proper in *. unfold respectful in *. intros. destruct Eq. split.
    intros. apply (Equivalence_Transitive y x y0). apply (Equivalence_Symmetric). auto.
    apply (Equivalence_Transitive x x0 y0). auto. auto.
    intros. apply (Equivalence_Transitive x y x0). auto.
    apply (Equivalence_Transitive y y0 x0). auto. apply Equivalence_Symmetric. auto.
  Qed.




  Instance mem_Proper : Proper (eq ==> FSetNat.Equal ==> eq) FSetNat.mem.
  Proof.
    intros. unfold Proper, respectful. intros. rewrite H. rewrite H0. reflexivity.
  Qed.


  
  Lemma proper_constax: forall (A B : Type) (SA : Setoid A) (SB : Setoid B) (b : B),
                          Proper (equiv ==> equiv) (fun _ : A => b).
      
  Proof.
    repeat autounfold. intros. reflexivity.
  Qed.
  Lemma id_Proper :
    forall A (SA : Setoid A),
      Proper (equiv ==> equiv) id.
  Proof.
    unfold Proper, respectful. auto.
  Qed.


    Definition constS {A B} {SA : Setoid A} (SB : Setoid B) : SA ~> SB ~~> SA.
    simple refine (injF2  (fun (a : A) ( _ : B) => a) _).
    Lemma constS_1 : forall {A B} {SA : Setoid A} (SB : Setoid B),
                       Proper (equiv ==> equiv ==> equiv)
                            ((fun (a : A) (_ : B)  => a)).
    Proof.
      autounfold. intros. auto.
    Qed.
    
    apply constS_1.
  Defined.
Section Utils.
  Context
    {A B C} {SA : Setoid A} {SB : Setoid B} {SC : Setoid C}.
  Definition idS : SA ~> SA.
    simple refine (injF  id _).
  Defined.
    


  Definition flipS : (SA ~~> SB ~~> SC) ~> (SB ~~> SA ~~> SC).
    simple refine (injF3  (fun (f : SA ~> SB ~~> SC) b a => f @ a @ b) _).
    Lemma flipS_1 : Proper (equiv ==> equiv ==> equiv ==> equiv)
     (fun (f : SA ~> SB ~~> SC) (b : B) (a : A) => f @ a @ b).
    Proof.
      autounfold. intros. rewritesr. 
    Qed.
    apply flipS_1.
    
  Defined.
End Utils.
   Program Instance unitS : Setoid unit.