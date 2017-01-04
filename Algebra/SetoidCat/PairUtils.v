Require Import Algebra.Tactics Algebra.Utils SetoidUtils Algebra.SetoidCat.

Require Import Coq.Lists.List RelationClasses Relation_Definitions Morphisms Coq.Program.Basics SetoidClass.

Open Scope type_scope.
  Definition liftPairR {A B} (RA: relation A) (RB: relation B) (ss1 ss2 : A * B) : Prop :=
    match ss1, ss2 with
      | (a, b), (c, d) => RA a c /\ RB b d
    end
  .

  Instance fst_Proper {A B} {RA : relation A} {RB : relation B} : Proper (liftPairR RA RB ==> RA) fst.
  Proof.
    unfold Proper, respectful, liftPairR. destruct x, y. simpl. intros. destruct H. auto.
  Qed.

  Instance snd_Proper {A B} {RA : relation A} {RB : relation B} : Proper (liftPairR RA RB ==> RB) snd.
  Proof.
    unfold Proper, respectful, liftPairR. destruct x, y. simpl. intros. destruct H. auto.
  Qed.
  Instance liftPairR_Reflexive {A B} {RA : relation A} {RB : relation B} : Reflexive RA -> Reflexive RB -> Reflexive (liftPairR RA RB).
  Proof.
    unfold Reflexive, liftPairR. intros. destruct x. split. apply H. apply H0.
  Qed.
  Instance pair_Proper {A B} {RA : relation A} {RB : relation B} : Proper (RA ==> RB ==> liftPairR RA RB) pair.
  Proof.
    unfold Proper, respectful. intros. split. auto. auto.
  Qed.


  Instance liftPairR_Symmetric {A B} {RA : relation A} {RB : relation B} : Symmetric RA -> Symmetric RB -> Symmetric (liftPairR RA RB).
  Proof.
    unfold Symmetric, liftPairR. intros. destruct x. destruct y. destruct H1. split. auto. auto.
  Qed.
  Instance liftPairR_Transitive {A B} {RA : relation A} {RB : relation B} : Transitive RA -> Transitive RB -> Transitive (liftPairR RA RB).
  Proof.
    unfold Transitive, liftPairR. intros. destruct x. destruct y. destruct z. destruct H1. destruct H2. split.  apply H with (y:=a0). auto. auto. apply H0 with (y := b0). auto. auto.
  Qed.

  Program Instance liftPairR_Equivalence {A B} {RA : relation A} {RB : relation B} : Equivalence RA -> Equivalence RB -> Equivalence (liftPairR RA RB).

  Instance equiv_equiv_Proper {A} {R : relation A} (Eq: Equivalence R) : Proper (R ==> R ==> iff) R.
  Proof.
    unfold Proper in *. unfold respectful in *. intros. destruct Eq. split.
    intros. apply (Equivalence_Transitive y x y0). apply (Equivalence_Symmetric). auto.
    apply (Equivalence_Transitive x x0 y0). auto. auto.
    intros. apply (Equivalence_Transitive x y x0). auto.
    apply (Equivalence_Transitive y y0 x0). auto. apply Equivalence_Symmetric. auto.
  Qed.

  Instance liftPairR_Proper {A B} {RA : relation A} {RB : relation B} : Equivalence RA -> Equivalence RB -> Proper (liftPairR RA RB ==> liftPairR RA RB ==> iff) (liftPairR RA RB).
  Proof.
    intros. apply equiv_equiv_Proper. apply liftPairR_Equivalence. auto. auto.
  Qed.

  Program Instance pairSetoid {A B} (SA : Setoid A) (SB : Setoid B) : Setoid (A * B).

  Notation "SA ~*~ SB" := (pairSetoid SA SB) (at level 20, left associativity).
  Hint Unfold liftPairR.


  Definition uncurryS {A B C} {SA : Setoid A} {SB : Setoid B} {SC : Setoid C} :
    (SA ~~> SB ~~> SC) ~> (SA ~*~ SB ~~> SC).
    simple refine (injF2 (fun f ab => f @ (fst ab) @ (snd ab)) _).
    Lemma uncurryProper_1 : forall {A B C} {SA : Setoid A} {SB : Setoid B} {SC : Setoid C},
                            Proper (equiv ==> equiv ==> equiv)
                                   (fun (f : SA ~> SB ~~> SC) (ab : A * B) => f @ fst ab @ snd ab).
    Proof.
      intros. solve_proper.
    Qed.
    apply uncurryProper_1.
  Defined.
    Definition curryS {A B C} {SA : Setoid A} {SB : Setoid B} {SC : Setoid C} :
    (SA ~*~ SB ~~> SC) ~> (SA ~~> SB ~~> SC).
    simple refine (injF3 (fun f a b => f @ (a, b)) _).
    Lemma curryProper_1 : forall {A B C} {SA : Setoid A} {SB : Setoid B} {SC : Setoid C},
                            Proper (equiv ==> equiv ==> equiv ==> equiv)
                                   (fun (f : SA ~*~ SB ~> SC) (a : A) (b : B) => f @ ( a, b)).
    Proof.
      intros. solve_proper.
    Qed.
    apply curryProper_1.
  Defined.

Section CompNProper.
  Context
    {A B C D E} {SA : Setoid A} {SB : Setoid B} {SC : Setoid C} {SD : Setoid D}  {SE: Setoid E}.
  Definition comp2S :
    (SA ~~> SB ~~> SC) ~> (SC ~~> SD) ~~> (SA ~~> SB ~~> SD).
    simple refine (injF4 (fun f g a b => g @ (f @ a @ b)) _).
    Lemma comp2Proper_1 : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv)
                                 (fun (f : SA ~> SB ~~> SC) (g : SC ~> SD) (a : A) (b : B) =>
                                    g @ (f @ a @ b)).
      solve_proper.
    Qed.
    apply comp2Proper_1.
  Defined.
  
  Definition comp3S :
    (SA ~~> SB ~~> SC ~~> SD) ~> (SD ~~> SE) ~~> (SA ~~> SB ~~> SC ~~> SE).
    simple refine (injF5 (fun f g a b c => g @ (f @ a @ b @ c)) _).
    Lemma comp3Proper_1 : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv ==> equiv)
                                 (fun (f : SA ~> SB ~~> SC ~~> SD) (g : SD ~> SE) (a : A) (b : B) (c : C) =>
                                    g @ (f @ a @ b @ c)).
      solve_proper.
    Qed.
    apply comp3Proper_1.
  Defined.
End CompNProper.

Section ProductF.

  Context
    {A B C D} {SA : Setoid A} {SB : Setoid B} {SC : Setoid C} {SD : Setoid D}.

  Definition productF :
    ( SA ~~> SB ) ~> (SC ~~> SD) ~~> (SA ~*~ SC) ~~> (SB ~*~ SD).
    refine (injF3 (fun (f : SA ~> SB) ( g : SC ~> SD) (p : A * C) => let (a, c) := p in (f @ a, g @ c)) _).
    Lemma productF_1 : Proper (equiv ==> equiv ==> equiv ==> equiv)
     (fun (f : SA ~> SB) (g : SC ~> SD) (p : A * C) =>
      let (a, c) := p in (f @ a, g @ c)).
    Proof.
      autounfold. intros. simpl_let. split. rewritesr. rewritesr.
    Qed.
    apply productF_1.
  Defined.

End ProductF.

Section PairingF.
  Context
    {A B C D} {SA : Setoid A} {SB : Setoid B} {SC : Setoid C} {SD : Setoid D}.
  
  Definition pairingF :
    ( SA ~~> SB ) ~> (SA ~~> SC) ~~> SA ~~> (SB ~*~ SC).
    refine (injF3 (fun (f : SA ~> SB) ( g : SA ~> SC) (a : A) => (f @ a, g @ a)) _).
    Lemma pairingF_1 : Proper (equiv ==> equiv ==> equiv ==> equiv)
     (fun (f : SA ~> SB) (g : SA ~> SC) (a : A) =>
      (f @ a, g @ a)).
    Proof.
      autounfold. intros. split. rewritesr. rewritesr.
    Qed.
    apply pairingF_1.
  Defined.

End PairingF.
Definition  fstS {A B} {AS : Setoid A} {BS : Setoid B} : AS ~*~ BS ~> AS.
  simple refine (injF fst _).
Defined.
Definition  sndS {A B} {AS : Setoid A} {BS : Setoid B} : AS ~*~ BS ~> BS.
  simple refine (injF snd _).
Defined.

  Notation "a *** b" := (productF @ a @ b) (at level 40, left associativity).
  Notation "a &&& b" := (pairingF @ a @ b) (at level 40, left associativity).

    Definition pairS {A B} {AS : Setoid A} {BS : Setoid B} : AS ~>  BS ~~> AS ~*~ BS := curryS @ idS.


    Lemma pairing_comp :
      forall {A} {AS : Setoid A} {B} {BS : Setoid B} {C} {CS : Setoid C}
             {D} {DS : Setoid D} {E} {ES : Setoid E} {F} {FS : Setoid F}
             (f : AS ~> CS) (g : BS ~> DS) (h : CS ~> ES) (i : DS ~> FS),
        (h *** i) ∘ (f *** g) == (h ∘ f) *** (i ∘ g).
    Proof.
      intros. simpl_equiv. destruct a. reflexivity. 
    Qed.
