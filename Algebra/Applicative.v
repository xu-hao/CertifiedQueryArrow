Require Import SetoidCat SetoidUtils Functor Monoid PairUtils Utils.

Require Import SetoidClass.

Section Applicative.

  Context
    {t : forall A, Setoid A -> Type}
    {tS : forall A (AS : Setoid A), Setoid (t A AS)}
    {func : @Functor t tS}.

  Definition left_unitor {A} {AS : Setoid A} : unitS ~*~ AS ~> AS := sndS.

  Definition right_unitor {A} {AS : Setoid A} : AS ~*~ unitS ~> AS := fstS. 
  
  Definition associator {A B C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C} : (AS ~*~ BS) ~*~ CS ~> AS ~*~ (BS ~*~ CS) := (fstS ∘ fstS) &&& ((sndS ∘ fstS) &&& sndS).
                              
  Class Applicative :=
    {
      unitA :  t unit _;
      prod {A B} {AS : Setoid A} {BS : Setoid B} : tS _ AS ~> tS _ BS ~~> tS _ (AS ~*~ BS);
      
      left_unit_applicative :
        forall {A} {AS : Setoid A} (a : t A _),
          left_unitor <$> (prod  @ unitA @ a) == a;
      right_unit_applicative :
        forall {A} {AS : Setoid A} (a : t A _),
          right_unitor <$> (prod  @ a @ unitA) == a;
      associativity_applicative:
        forall {A B C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C}
               (a : t A _) (b : t B _) (c : t C _) ,
          associator <$> (prod  @ (prod  @ a @ b) @ c) == prod  @ a @ (prod  @ b @ c);
      naturality_prod:
        forall {A B C D} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C} {DS : Setoid D}
               (f : AS ~> BS) (g : CS ~> DS) (a : t A _) (c : t C _),
          prod  @ (f <$> a) @ (g <$> c) == (f *** g) <$> (prod  @ a @ c)
    }.

  Context
    {app : Applicative}.

  Definition pure  {A} {AS : Setoid A} : AS ~> tS _ AS := (flipS @ fmap @ unitA) ∘ constS unitS.

  Definition ap {A B} {AS : Setoid A} {BS : Setoid B} : tS _ (AS ~~> BS) ~> tS _ AS ~~> tS _ BS :=
    comp2S @ prod @ (fmap @ (uncurryS @ evalS)).

  Definition produ {A B} {AS : Setoid A} {BS : Setoid B} : tS _ AS ~*~ tS _ BS ~> tS _ (AS ~*~ BS) := uncurryS @ prod  .


  
End Applicative.


Notation "a ** b" := (prod @ a @ b) (at level 49, left associativity).
Notation "a <*> b" := (ap @ a @ b) (at level 49, left associativity).

Section IdentityApplicative.


  Definition idFunc_unitA := IdentityIso unit tt.
  Definition idFunc_prod {A B} {AS : Setoid A} {BS : Setoid B} : IdentityS AS ~> IdentityS BS ~~> IdentityS (AS ~*~ BS) :=
    flipS @ compS @ IdentityIsoS (AS ~*~ BS)
          ∘ compS @ IdentityIsoS' BS
          ∘ curryS @ @idS _ (AS ~*~ BS) ∘ IdentityIsoS' AS.

  Existing Instance IdentityFunctor.
  Existing Instance IdentityS.

  Instance Identity_Applicative : @Applicative IdentityFunc _ _.
  
  Proof.

    exists (@idFunc_unitA) (@idFunc_prod).
    
    intros. simpl. destruct a. reflexivity.
    intros. simpl. destruct a. reflexivity. 
    intros. simpl. split. reflexivity. split. reflexivity. reflexivity.
    intros. simpl. split. reflexivity. reflexivity.
  Defined.
End IdentityApplicative.

Section ComposeApplicative.

  Context
    {t t' : forall A, Setoid A -> Type}
    {tS : forall A (AS : Setoid A), Setoid (t A AS)}
    {tS' : forall A (AS : Setoid A), Setoid (t' A AS)}
    {func : @Functor t tS} {func' : @Functor t' tS'}
    {app : @Applicative _ _ func} {app' : @Applicative _ _ func'}.


  Definition compFunc_unit : @ComposeFunc t t' _ unit _  := ComposeIsoS unitS @ (pure @ unitA).

  Definition compFunc_prod {A B} {AS : Setoid A} {BS : Setoid B} : @ComposeS t t' _ _ _ AS ~> @ComposeS t t' _ _ _ BS ~~> @ComposeS t t' _ _ _ (AS ~*~ BS) :=
    flipS @ compS @ ComposeIsoS (AS ~*~ BS)
          ∘ compS @ ComposeIsoS' BS
          ∘ comp2S  @  prod  @ (fmap @ produ) ∘ ComposeIsoS' AS.

  Existing Instance ComposeFunctor.
  Existing Instance ComposeS.

  Lemma compFunc_naturality_prod:
    forall {A B C D} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C} {DS : Setoid D}
           (f : AS ~> BS) (g : CS ~> DS) (a : ComposeFunc A) (c : ComposeFunc C),
      compFunc_prod @ (compFunc_fmap @ f @ a) @ (compFunc_fmap @ g @ c) == compFunc_fmap @ (f *** g) @ (compFunc_prod @ a @ c).
  Proof.
    intros. unfold compFunc_fmap. unfold compFunc_prod. simpl. rewrite naturality_prod. rewrite fmap_fmap. rewrite fmap_fmap. evalproper. evalproper. simpl. arrequiv. destruct a0. simpl. rewrite naturality_prod. evalproper. 
  Qed.
  

  Instance Compose_Applicative : @Applicative (@ComposeFunc t t' _ ) (@ComposeS t t' _ _) _.
  Proof.
    exists (@compFunc_unit) (@compFunc_prod).
    intros. simpl. destruct a. simpl. rewrite <- (fmap_idS_absorb t0) at 1.  rewrite naturality_prod. rewrite fmap_fmap. rewrite fmap_fmap. rewrite <- (left_unit_applicative t0) at 2. evalproper. evalproper. simpl. arrequiv. destruct a. simpl. rewrite left_unit_applicative. reflexivity.
    intros. simpl. destruct a. simpl. rewrite <- (fmap_idS_absorb t0) at 1.  rewrite naturality_prod. rewrite fmap_fmap. rewrite fmap_fmap. rewrite <- (right_unit_applicative t0) at 2. evalproper. evalproper. simpl. arrequiv. destruct a. simpl. rewrite right_unit_applicative. reflexivity.
    intros. simpl. rewrite <- (fmap_idS_absorb (ComposeIso' C c)) at 1. rewrite naturality_prod. rewrite <- (fmap_idS_absorb (ComposeIso' A a)) at 2. rewrite naturality_prod. rewrite <- associativity_applicative. repeat rewrite fmap_fmap. evalproper. evalproper. simpl. arrequiv. destruct a0. simpl. apply associativity_applicative.
    intros. apply compFunc_naturality_prod.
  Defined. 
  

End ComposeApplicative.

Section ConstApplicative.
  Context
    {C}
    {CS : Setoid C}
    {mon : @Monoid C CS}.

  Definition constFunc_unitA := ConstIsoS CS unitS @ mempty.
  Definition constFunc_prod {A B} {AS : Setoid A} {BS : Setoid B} : ConstS CS AS ~> ConstS CS BS ~~> ConstS CS (AS ~*~ BS) :=
    flipS @ compS @ ConstIsoS CS (AS ~*~ BS)
          ∘ compS @ ConstIsoS' CS BS
          ∘ mappend ∘ ConstIsoS' CS AS.

  Existing Instance ConstFunctor.
  Existing Instance ConstS.

  Instance Const_Applicative : @Applicative (ConstFunc C) _ _.
  
  Proof.

    exists (@constFunc_unitA) (@constFunc_prod).
    
    intros. simpl. destruct a. rewrite left_unit_monoid. reflexivity.
    intros. simpl. destruct a. rewrite right_unit_monoid. reflexivity. 
    intros. simpl. rewrite associativity_monoid. reflexivity. 
    intros. simpl. reflexivity. 
  Defined.
End ConstApplicative.

Section Utils.
  Context
    {t: forall A, Setoid A -> Type}
    {tS : forall A (AS : Setoid A), Setoid (t A AS)}
    {func : @Functor t tS}
    {app : @Applicative _ _ func}.
  (* some general lemmas *)

  Lemma idS_absorb : forall {A} {AS : Setoid A} (a : A), idS @ a == a.
  Proof.
    intros. simpl. reflexivity.
  Qed.

  Lemma fmap_pure : forall {A B} {AS : Setoid A} {BS : Setoid B} (f : AS ~> BS) (a :  A),
                      f <$> pure @ a == pure @ (f @ a).
  Proof.
    intros. simpl. rewrite fmap_fmap.
    evalproper.    evalproper. simpl. arrequiv. 
  Qed.

  Lemma uncurry_fmap_prod : forall {A B C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C} (f : AS ~> BS ~~> CS) (a : t A _) (b : t B _),
                             uncurryS @  f <$>  (a ** b) ==  f <$> a <*> b.
  Proof.
    intros. unfold ap. unfold comp2S. normalize. rewrite <- (fmap_idS_absorb b) at 2. rewrite naturality_prod. rewrite fmap_fmap. evalproper. evalproper. simpl. arrequiv.  destruct a0. simpl. reflexivity.
  Qed.

  Lemma evalS_idem : forall {A B} {AS : Setoid A} {BS : Setoid B},
                      @evalS _ _ AS BS ∘ @evalS _ _ AS BS == @evalS _ _ AS BS.

  Proof.
    intros.  simpl_equiv. simpl_equiv. reflexivity. 
  Qed.
  Lemma fmap_eval : forall {A B} {AS : Setoid A} {BS : Setoid B} (f : t (AS ~> BS) _) (a : t  A _),
                      evalS <$> f <*> a == f <*> a.

  Proof.
    intros. unfold ap, comp2S. normalize. rewrite uncurry_fmap_prod . rewrite uncurry_fmap_prod.  rewrite fmap_fmap. rewrite evalS_idem. reflexivity.
  Qed.
  Lemma ap_pure : forall {m mS}
                       {func}
                       {app : @Applicative m mS func}
                       {A B : Type}
                       {SA : Setoid A}
                       {SB : Setoid B} (f : SA ~> SB ) (a : m A _), pure @ f <*> a == f <$> a.
  Proof.
    intros. simpl.  rewrite <- (fmap_idS_absorb a) at 1. rewrite naturality_prod. rewrite fmap_fmap. rewrite <- (left_unit_applicative a) at 2. rewrite fmap_fmap. evalproper. evalproper. simpl. arrequiv. destruct a0.  reflexivity.

  Qed.

  Lemma applicative_id: forall {A} {AS : Setoid A} {a : t A _},
                         (pure @ @idS _ AS) <*> a == a.
  Proof.
    intros. unfold ap, comp2S. normalize. unfold pure, comp, flipS. normalize. rewrite <- (idS_absorb a) at 1. rewrite <- functoriality_id.  rewrite naturality_prod. rewrite fmap_fmap. 
    rewrite <- (left_unit_applicative a) at 2. evalproper. evalproper. simpl. arrequiv. destruct a0. reflexivity.
  Qed.
  
  Lemma applicative_comp :
        forall {A B C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C}
               (f : t (AS ~> BS) _) (g : t (BS ~> CS) _) (a  : t A _),
          pure @ (flipS @ compS) <*>  g <*>  f <*> a ==
          g <*> ( f <*> a).
  Proof.
    intros. simpl.  arrequiv. 
    rewrite <- (fmap_idS_absorb g) at 1. rewrite naturality_prod at 1.
    rewrite <- (fmap_idS_absorb f). rewrite fmap_fmap.  rewrite naturality_prod at 1.
    rewrite <- (fmap_idS_absorb a). rewrite fmap_fmap.   rewrite naturality_prod at 1.
    rewrite naturality_prod at 1.
    rewrite <- (left_unit_applicative g) at 2. rewrite fmap_fmap.   rewrite fmap_fmap. rewrite naturality_prod.
    rewrite <- (associativity_applicative (unitA ** g) f a).
    rewrite (fmap_fmap).
    rewrite (fmap_fmap).
    evalproper.  evalproper. simpl.
arrequiv. destruct a0. destruct p. destruct p. simpl. reflexivity.

  Qed.
  
  Lemma applicative_homomorphism :
    forall {A B} {AS : Setoid A} {BS : Setoid B}
           (f : AS ~> BS) (a : A),
      pure @ f <*> pure @ a == pure @ (f @ a).
  Proof.
    intros. simpl. rewrite naturality_prod. rewrite <- (left_unit_applicative unitA) at 3. rewrite fmap_fmap. rewrite (fmap_fmap). evalproper.  evalproper. simpl. arrequiv. destruct a0. reflexivity.
  Qed.
  
  Lemma applicative_interchange:
    forall {A B} {AS : Setoid A} {BS : Setoid B}
           (f : t (AS ~> BS) _) (a : A),
      f <*> (pure @ a) == pure @ (flipS @ evalS @ a) <*> f.
  Proof.
    intros. simpl. 
    rewrite <- (left_unit_applicative f) at 1.
    rewrite <- (fmap_idS_absorb f) at 2.
    rewrite naturality_prod.
    rewrite naturality_prod.
    rewrite <- (right_unit_applicative (unitA ** f)) at 2.
    rewrite fmap_fmap.
    rewrite (fmap_fmap). 
    rewrite (fmap_fmap).
    evalproper. evalproper. simpl. arrequiv. destruct a0. simpl. destruct p. reflexivity.
  Qed.
End Utils.


Class ApplicativeTransformation  {t t' tS tS'} {func : @Functor t tS} {app' : @Applicative t tS func} {func' : @Functor t' tS'} {app': @Applicative t' tS' func'}
        (tr : forall {A} {AS : Setoid A}, tS _ AS ~> tS' _ AS) :=
  {
    app_trans_unit : tr @ unitA == unitA;
    app_trans_prod : forall {A B} {AS : Setoid A} {BS : Setoid B} (a : t A _)(b : t B _), tr @ (a ** b) == (tr @ a) ** (tr @ b);
    app_trans_naturality : forall {A B} {AS : Setoid A} {BS : Setoid B} (a : t A _) (f: AS ~> BS), tr @ (f <$> a) == f <$> tr @ a;
  }.

Lemma app_trans_pure : forall {t t' tS tS'} {func : @Functor t tS} {func' : @Functor t' tS'} {app' : @Applicative t tS func}  {app': @Applicative t' tS' func'} {A} {AS : Setoid A}
                              (tr : forall {A} {AS : Setoid A}, tS _ AS ~> tS' _ AS),
                         ApplicativeTransformation (@tr) -> forall (a: A),
                         tr @ (pure @ a) == pure @ a.
Proof.
  intros. unfold pure. unfold flipS. normalizecomp. rewrite (app_trans_naturality). rewrite app_trans_unit. reflexivity.
Qed.

Lemma app_trans_ap : forall {t t' tS tS'} {func : @Functor t tS} {func' : @Functor t' tS'} {app' : @Applicative t tS func} {app': @Applicative t' tS' func'} {A B} {AS : Setoid A} {BS : Setoid B}
                            (tr : forall {A} {AS : Setoid A}, tS _ AS ~> tS' _ AS),
                       ApplicativeTransformation (@tr) -> forall (a: t A _) (f : t (AS ~> BS) _),
                                                            tr @ (f <*> a) == tr @ f <*> tr @ a.
Proof.
  intros. unfold ap. unfold comp2S. normalize. rewrite app_trans_naturality. rewrite app_trans_prod. reflexivity.
Qed.
