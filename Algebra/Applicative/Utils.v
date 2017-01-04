Require Import SetoidCat SetoidUtils Algebra.Functor Algebra.Monoid PairUtils Algebra.Utils UnitUtils Algebra.Applicative Algebra.Functor.Utils.

Require Import SetoidClass.

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


