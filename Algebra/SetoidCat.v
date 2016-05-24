Require Import  Utils.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Open Scope type_scope.


Section SetoidCat.
 

  Definition arr {A B} (SA : Setoid A) (SB : Setoid B) :=
    { f : A -> B | Proper (equiv ==> equiv) f }.

  Notation "SA ~> SB" := (arr SA SB) (at level 99, right associativity).

  Definition injF
             {A B}  {SA : Setoid A} {SB : Setoid B} (f : A -> B)
             (pr : Proper (equiv ==> equiv) f) : SA ~> SB :=
    exist (Proper (equiv ==> equiv)) f pr
  .

  Definition projF
             {A B} {SA : Setoid A} {SB : Setoid B} (f : SA ~> SB) : A -> B :=
    proj1_sig f.

  Definition eval {A B} {SA : Setoid A} {SB : Setoid B} (f : SA ~> SB) (a : A) :=
    projF f a.

  Definition arrEquiv {A B} {SA : Setoid A} {SB : Setoid B} (m m2 : SA ~> SB) := forall a, eval m a == eval m2 a.

  Hint Unfold arr eval arrEquiv.

  Global Instance arr_Equivalence {A B} {SA : Setoid A} {SB : Setoid B} : Equivalence (@arrEquiv A B SA SB).
  Proof.
    split.
    autounfold. intros. reflexivity.
    autounfold. intros. symmetry. auto.
    autounfold. intros. transitivity (eval y a). apply H. apply H0.
  Qed.

  Global Program  Instance arrSetoid {A B} (SA : Setoid A) (SB : Setoid B) : Setoid (SA ~> SB) :=
    {
      equiv := arrEquiv
    }.

  Definition exp {B A} (SB : Setoid B) (SA : Setoid A) := arrSetoid SA SB.

  Global Instance eval_Proper A B (SA : Setoid A) (SB : Setoid B) : Proper (equiv ==> equiv ==> equiv) (@eval A B SA SB).
  Proof.
    unfold Proper, respectful. intros. destruct x, y. simpl in *. transitivity (x1 x0).
    apply H.
    rewrite H0. reflexivity.
  Qed.

  Definition comp {A B C} {SA : Setoid A} {SB : Setoid B} {SC : Setoid C} (f : SA ~> SB) (g : SB ~> SC) : SA ~> SC.
    simple refine (injF (fun a => eval g (eval f a)) _).
    Lemma comp_1 : forall {A B C} {SA : Setoid A} {SB : Setoid B} {SC : Setoid C} (f : SA ~> SB) (g : SB ~> SC), Proper (equiv ==> equiv) (fun a : A => eval g (eval f a)).
    Proof.
      unfold Proper, respectful. intros. rewrite H. reflexivity.
    Qed.
    apply comp_1.
  Defined.


  Global Instance comp_Proper A B C (SA : Setoid A) (SB : Setoid B) (SC : Setoid C) : Proper (equiv ==> equiv ==> equiv) (@comp A B C SA SB SC).
  Proof.
    unfold Proper, respectful. intros. simpl. unfold arrEquiv. intros. unfold eval, comp. simpl. rewrite H, H0. reflexivity.
  Qed.

  Lemma fun_ext : forall
                    A B (SA : Setoid A) (SB : Setoid B) (f g : SA ~> SB),
                    (forall (a : A),
                      eval f a == eval g a) -> f == g.
  Proof.
    intros. unfold equiv. simpl.  auto.
  Qed.

End SetoidCat.

Notation "SA ~> SB" := (arr SA SB) (at level 30, right associativity).
Notation "f @ a" := (eval f a) (at level 20, left associativity).
Notation "SA ~~> SB" := (exp SB SA) (at level 30, right associativity).
Notation "g ∘ f" := (comp f g) (at level 40, left associativity).


  Ltac proper :=
    let H1 := fresh "H" in
    match goal with
      | |- exists _ : ?H, _ => assert H as H1 ; [
            intros; unfold Proper, respectful; intros |
            exists H1 ]
    end.

  Ltac arrequiv :=
    repeat match goal with
      | |- injF ?f _ == injF ?g _ =>
        unfold equiv ; repeat match goal with
                                | |- ?a _ _ => simpl a
                              end
      | |- arrEquiv _ _ =>
        unfold arrEquiv; intros; simpl; try reflexivity;
        try match goal with
              | H : ?a == _ |- context [?a] => rewrite H; reflexivity
            end
    end.


Lemma projF_injF A B (SA : Setoid A ) (SB : Setoid B) :
  forall (f : A -> B) p,
    projF (injF f p) = f.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma eval_injF : forall A B (SA : Setoid A) (SB : Setoid B)
                   a (f : A -> B) pr,
                    injF f pr @ a = f a.
Proof.
  intros. simpl. reflexivity.
Qed.

Definition injF2 {A B C} {SA : Setoid A} {SB : Setoid B} {SC : Setoid C} (f : A -> B -> C) (pr : Proper (equiv ==> equiv ==> equiv) f) : SA ~> SB ~~> SC.
  simple refine (injF (fun a => injF (f a) _) _).

  Lemma proper_xx : forall A B C (SA : Setoid A) (SB : Setoid B) (SC : Setoid C) (f : A -> B -> C) a, Proper (equiv ==> equiv ==> equiv) f -> Proper (equiv ==> equiv) (f a).
  Proof.
     intros. autounfold. solve_proper. 
  Qed.
  apply (proper_xx _ _ _ SA). auto.
  Lemma injF2_1 :  forall A B C (SA : Setoid A) (SB : Setoid B) (SC : Setoid C) (f : A -> B -> C) pr, Proper (equiv ==> equiv ==> equiv) f -> Proper (equiv ==> equiv) (fun a : A => injF (f a) (pr a)).
  Proof.
    intros. autounfold. unfold Proper, respectful.  intros. arrequiv. 
  Qed.
  apply injF2_1. auto.
Defined.

Section InjF3.
  Context
               {A B C D}
           {SA : Setoid A} {SB : Setoid B} {SC : Setoid C} {SD : Setoid D}
           (f : A -> B -> C -> D)
           (pr : Proper (equiv ==> equiv ==> equiv ==> equiv) f).
  
Definition injF3 :
  SA ~> SB ~~> SC ~~> SD.
  simple refine (injF (fun a => injF2 (f a) _) _).
Lemma injF3_1: forall a, Proper (equiv ==> equiv ==> equiv) (f a).
Proof.
  intros. 
  solve_proper.
Qed.
apply injF3_1.
Lemma injF3_2 : forall pr, Proper (equiv ==> equiv) (fun a : A => injF2 (f a) (pr a)).
Proof.
  autounfold. unfold Proper, respectful. intros. unfold injF2. arrequiv.
Qed.
apply injF3_2.
Defined.
End InjF3.

Section InjF4.
  Context
               {A B C D E}
           {SA : Setoid A} {SB : Setoid B} {SC : Setoid C} {SD : Setoid D} {SE : Setoid E}
           (f : A -> B -> C -> D -> E)
           (pr : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) f).
  
Definition injF4 :
  SA ~> SB ~~> SC ~~> SD ~~> SE.
  simple refine (injF (fun a => injF3 (f a) _) _).
Lemma injF4_1: forall a, Proper (equiv ==> equiv ==> equiv ==> equiv) (f a).
Proof.
  intros. 
  solve_proper.
Qed.
apply injF4_1.
Lemma injF4_2 : forall pr, Proper (equiv ==> equiv) (fun a : A => injF3 (f a) (pr a)).
Proof.
  autounfold. intros. unfold Proper, respectful. intros. unfold injF3. arrequiv.
Qed.
apply injF4_2.
Defined.
End InjF4.
Section InjF5.
  Context
               {A B C D E F}
           {SA : Setoid A} {SB : Setoid B} {SC : Setoid C} {SD : Setoid D} {SE : Setoid E} {SF : Setoid F}
           (f : A -> B -> C -> D -> E -> F)
           (pr : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv ==> equiv) f).
  
Definition injF5 :
  SA ~> SB ~~> SC ~~> SD ~~> SE ~~> SF.
  simple refine (injF (fun a => injF4 (f a) _) _).
Lemma injF5_1: forall a, Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) ( f a).
Proof.
  intros. 
  solve_proper.
Qed.
apply injF5_1.
Lemma injF5_2 : forall pr, Proper (equiv ==> equiv) (fun a : A => injF4 (f a) (pr a)).
Proof.
  autounfold. intros. unfold Proper, respectful. intros. unfold injF4. arrequiv.
Qed.
apply injF5_2.
Defined.
End InjF5.
Section InjF6.
  Context
               {A B C D E F G}
           {SA : Setoid A} {SB : Setoid B} {SC : Setoid C} {SD : Setoid D} {SE : Setoid E} {SF : Setoid F} {SG : Setoid G}
           (f : A -> B -> C -> D -> E -> F -> G)
           (pr : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv ==> equiv ==> equiv) f).
  
Definition injF6 :
  SA ~> SB ~~> SC ~~> SD ~~> SE ~~> SF ~~> SG.
  simple refine (injF (fun a => injF5 (f a) _) _).
Lemma injF6_1: forall a, Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv ==> equiv) (f a).
Proof.
  intros. 
  solve_proper.
Qed.
apply injF6_1.
Lemma injF6_2 : forall pr, Proper (equiv ==> equiv) (fun a : A => injF5 (f a) (pr a)).
Proof.
  autounfold. intros. unfold Proper, respectful. intros. unfold injF5. arrequiv.
Qed.
apply injF6_2.
Defined.
End InjF6.

Definition compS {A B C} {SA : Setoid A} {SB : Setoid B} {SC : Setoid C} :
  (SA ~~> SB) ~> (SB ~~> SC) ~~> (SA ~~> SC).
  simple refine (injF2 comp _).
Defined.

  (*
Definition evalProper {A B} {SA : Setoid A} {SB : Setoid B} :
  (SA ~~> SB) ~> SA ~~> SB.
  simple refine (injF2 eval _).
Defined.
*)

Program Instance funcS A B (SA : Setoid A) (SB : Setoid B) : Setoid (A -> B) :=
  {
    equiv := pointwise_relation A equiv
  }.


Definition injective {A B} (SA : Setoid A) (SB : Setoid B) (f : SA ~> SB) := forall a b, f @ a == f @ b -> a == b.

Hint Unfold Proper respectful.

Ltac evalproper := apply eval_Proper; [try reflexivity | try reflexivity].

Ltac normalizeHyp H := repeat (repeat unfold injF2, injF3, injF4, injF5, injF6 in H; rewrite eval_injF in H).

Ltac normalize := repeat (repeat unfold injF2, injF3, injF4, injF5, injF6; rewrite eval_injF).
Ltac normalizecomp := repeat (repeat unfold comp, injF2, injF3, injF4, injF5, injF6; rewrite eval_injF).
Ltac simpl_equiv := unfold equiv;
  match goal with
    | |- ?eq _ _ => simpl eq
  end;
  unfold arrEquiv; intros;  normalize.

  Definition evalS {A B} {AS : Setoid A} {BS : Setoid B} := injF2  (@eval _ _ AS BS) _.


