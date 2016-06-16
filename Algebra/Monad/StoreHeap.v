Require Import  Utils Algebra.SetoidCat Algebra.Monad Algebra.Monoid  Algebra.Alternative Algebra.NearSemiRing  Algebra.Monad.ContT Algebra.Alternative Algebra.Functor Algebra.Applicative PairUtils SetoidUtils Tactics Algebra.SetoidCat.UnitUtils Algebra.Monoid.ArrUtils.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Open Scope type_scope.


  

Section StoreHeap.
  Context
    {H : Type} {SH : Setoid H}
    {R : Type} {SR : Setoid R}
    {l lS}
    {alt : @Alternative l lS}
  .

  Definition storeHeap A {AS} := SH ~> SR ~~> SH ~*~ lS (R * A) (SR ~*~ AS).
  Instance storeHeapS {A} AS : Setoid (@storeHeap A AS) := SH ~~> SR ~~> SH ~*~ lS (R * A) (SR ~*~ AS).

  Definition sh {B} (BS : Setoid B) A {SA : Setoid A} := contT BS (@storeHeapS) A.
  Definition shS {B}  (BS : Setoid B) { A} (SA : Setoid A):= contTS BS (@storeHeapS) SA.

  Definition runSh {A B} {SA : Setoid A} {BS : Setoid B} : shS BS SA ~> (SA ~~> storeHeapS BS) ~~> storeHeapS BS := runContT.

  Existing Instance contT_Monad.
  
  Definition storeHeap_empty {A} {AS : Setoid A} : storeHeap A.
    simple refine (injF (fun h : H => constS SR @ (h, empty)) _).
    exact lS.
    exact alt.
    Lemma storeHeap_empty_1: forall {A} {AS : Setoid A}, Proper (equiv ==> equiv) (fun h : H => constS SR @ (h, empty)).
    Proof.
      intros. solve_proper.
    Qed.
    apply storeHeap_empty_1.
  Defined.

  Definition storeHeap_append {A} {AS : Setoid A} : storeHeapS AS ~> storeHeapS AS ~~> storeHeapS AS.
    simple refine (injF4 (fun (s1 s2 : storeHeap A) h r =>
                           let (h', l1) := s1 @ h @ r in
                           let (h'', l2) := s2 @ h' @ r in
                           (h'', l1 <|> l2)) _).
    exact lS.
    exact alt.
    Lemma storeHeap_append_1 : forall {A} {AS : Setoid A}, Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv)
     (fun (s1 s2 : storeHeap A) (h : H) (r : R) =>
      let (h', l1) := s1 @ h @ r in
      let (h'', l2) := s2 @ h' @ r in (h'', l1 <|> l2)).
    Proof.
      autounfold. intros. simpl_let. split. rewritesr. rewritesr.
    Qed.
    apply storeHeap_append_1.
  Defined.

  Instance storeHeap_Alternative : @Alternative (@storeHeap) (@storeHeapS).
  Proof.
    exists (@storeHeap_empty) (@storeHeap_append).
    intros. simpl. arrequiv. simpl_let. destruct (a @ a0 @ a1). rewrite left_unit_alt. split. reflexivity. reflexivity.
    intros. simpl. arrequiv. simpl_let. destruct (a @ a0 @ a1). rewrite right_unit_alt. split. reflexivity. reflexivity.
    intros. simpl. arrequiv. simpl_let. destruct (a @ a0 @ a1). simpl. destruct (b @ h @ a1).  simpl. split . reflexivity. rewrite associativity_alt. reflexivity.
  Defined. 
  
  Instance sh_Monad {B} {BS : Setoid B} : @Monad (@sh B BS) (@shS B BS) := contT_Monad BS (@storeHeapS).

  Instance sh_Alternative {B} {BS : Setoid B} : @Alternative (@sh B BS) (@shS B BS) := contT_Alternative BS (@storeHeapS).

  Context
    {func : @Functor l lS}
    {app : @Applicative l lS func}.

  Definition getStore  {B} {BS : Setoid B} : sh BS R.
    simple refine (injF3 (fun (c : SR ~> storeHeapS BS) (h : H) (s : R)  => c @ s @ h @ s) _).
    Lemma getStore_1 : forall {B} {BS : Setoid B}, Proper (equiv ==> equiv ==> equiv ==> equiv)
                                 (fun (c : SR ~> storeHeapS BS) (h : H) (s : R) => c @ s @ h @ s).
    Proof.
      intros. solve_proper.
    Qed.
    apply getStore_1.
  Defined.

  Definition getHeap  {B} {BS : Setoid B} : sh BS H.
    simple refine (injF3 (fun (c : SH ~> storeHeapS BS) (h : H) (s : R)  => c @ h @ h @ s) _).
    Lemma getHeap_1 : forall {B} {BS : Setoid B}, Proper (equiv ==> equiv ==> equiv ==> equiv)
                                 (fun (c : SH ~> storeHeapS BS) (h : H) (s : R) => c @ h @ h @ s).
    Proof.
      intros. solve_proper.
    Qed.
    apply getHeap_1.
  Defined.

  Definition putStore  {B} {BS : Setoid B} : SR ~> shS BS unitS.
    simple refine (injF4 (fun (s : R) (c : unitS ~> storeHeapS BS) (h : H) (_ : R)  => c @ tt @ h @ s) _).
    Lemma putStore_1 : forall {B} {BS : Setoid B}, Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv)
     (fun (s : R) (c : unitS ~> storeHeapS BS) (h : H) (_ : R) =>
      c @ tt @ h @ s).
    Proof.
      autounfold. intros. rewritesr. 
    Qed.
    apply putStore_1.
  Defined.
  
  Definition updateStore {B} {BS : Setoid B} : (SR ~~> SR) ~> shS BS unitS := (bind @ getStore) ∘ (flipS @ compS @ putStore).  
             
  Definition putHeap  {B} {BS : Setoid B} : SH ~> shS BS unitS.
    simple refine (injF4 (fun (h : H) (c : unitS ~> storeHeapS BS) (_ : H) (s : R)  => c @ tt @ h @ s) _).
    Lemma putHeap_1 : forall {B} {BS : Setoid B}, Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv)
     (fun (h : H) (c : unitS ~> storeHeapS BS) (_ : H) (s : R) =>
      c @ tt @ h @ s).
    Proof.
      autounfold. intros. rewritesr. 
    Qed.
    apply putHeap_1.
  Defined.

  Definition updateHeap {B} {BS : Setoid B} : (SH ~~> SH) ~> shS BS unitS := (bind @ getHeap) ∘ (flipS @ compS @ putHeap).  

  Existing Instance arr_Monoid.
  Existing Instance contT_A_Monoid.

  Section Sh_SS_unitS_NearSemiRing.
    Definition sh_times {S : Type} {SS : Setoid S} : shS SS unitS ~> shS SS unitS ~~> shS SS unitS := andThen.

    Definition sh_plus {S : Type} {SS : Setoid S} : shS SS unitS ~> shS SS unitS ~~> shS SS unitS := mappend.

    Definition sh_zero {S : Type} {SS : Setoid S} : sh SS unit := mempty.

    Definition sh_one {S : Type} {SS : Setoid S}: sh SS unit := ret @ tt.

    
  Instance sh_NearSemiRing {S : Type} {SS : Setoid S} : @NearSemiRing _ (shS SS unitS).
  Proof.
    exists (sh_one) (sh_zero) (sh_times) (sh_plus).
    intros. simpl. arrequiv.    
    intros. unfold sh_times, sh_one. unfold andThen. normalizecomp. unfold constS. normalize. apply (@right_unit_equiv (sh SS) (@shS _ SS) sh_Monad). simpl. arrequiv. destruct a0. reflexivity.
    intros. unfold sh_times. unfold andThen. normalizecomp. rewrite (@associativity (@sh S SS) (@shS _ SS) sh_Monad _ _ _ _ _ _ a (constS unitS @ b) (constS unitS @ c)). evalproper. simpl_equiv. reflexivity.
    intros. apply left_unit_monoid.
    intros. apply right_unit_monoid.
    intros. apply associativity_monoid.
    intros. simpl. arrequiv.
    intros. unfold sh_times at 1. unfold sh_plus at 1.  unfold andThen. normalizecomp. rewrite (@contT_left_distributivity _ _ _ _ _ _ _ _ _ a b (constS _ @ c)). reflexivity.
    Grab Existential Variables.
    solve_proper.
  Defined.
  
End Sh_SS_unitS_NearSemiRing.
  (* Proof. *)

  
  (* Proof. *)

(*  
  
  Lemma concatMapM_cons : forall m0 (mnd : @Monad m0) A B (SA : Setoid A) (SB : Setoid B) (f : SA ~> m (listS SB)) (a : A) (l : list A), concatMapM @ f @ (a :: l) == appProper <$> f @ a <*> concatMapM @ f @ l.
  Proof.
    intros. simpl. repeat rewrite associativity_2. bindproper. unfold compM, injF2. simpl. arrequiv.
rewrite left_unit. simpl. normalize_monad. bindproper. normalize_monad.  reflexivity.
Grab Existential Variables.
solve_proper.
solve_proper.
  Qed.

  Lemma sequence_map_ret : forall m0 (mnd : @Monad m0) A B (SA : Setoid A) (SB : Setoid B) (l : list A) (f : A -> B), sequence (map (fun a => ret @ f a) l) == ret @ map f l.  
  Proof.
    intros. induction l.
    simpl. reflexivity.
    intros. simpl. normalize_monad. rewrite IHl. rewrite left_unit. simpl. reflexivity.
  Qed.

  
  Lemma concatMapM_ret : forall m0 (mnd : @Monad m0) A  (SA : Setoid A)  pr (l : list A) (s : H), injective (listS SA) (m (listS SA)) ret -> concatMapM @ injF (fun a => ret @ (a :: nil)) pr  == ret .
  Proof.
    intros. simpl. arrequiv. induction a. simpl. normalize_monad. reflexivity.
    simpl. normalize_monad. rewrite <- associativity0. rewrite ret_ret. rewrite <- ret_ret with (f:=@concat A) (g:=app (a::nil)).
    assert (forall pr, injF (fun a1 => ret @ concat a1) pr == ret ∘ concatProper). intros. apply fun_ext. intros. reflexivity. rewrite H1.
    rewrite IHa. normalize_monad. reflexivity. solve_proper. solve_proper. solve_proper. solve_proper.
    Grab Existential Variables.
    solve_proper.
    solve_proper.
    solve_proper.
    solve_proper.
    solve_proper.
  Qed.

    Lemma concatMapM_nil : forall m0 (mnd : @Monad m0) A B (SA : Setoid A) (SB : Setoid B) (f : SA ~> m (listS SB)), concatMapM @ f @ nil == ret @ nil.
  Proof.
    intros. simpl. rewrite left_unit. simpl. reflexivity.
  Qed. *)  

End StoreHeap.
