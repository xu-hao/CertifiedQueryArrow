Require Import  Utils Algebra.SetoidCat Algebra.Monad Algebra.Monoid  Algebra.Alternative Algebra.MonoidUtils Algebra.NearSemiRing Algebra.Store Algebra.ContT Algebra.Alternative Algebra.Functor Algebra.Applicative PairUtils SetoidUtils Tactics.

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


  Existing Instance arr_Monoid.
  Existing Instance contT_A_Monoid.

  Definition sh_times{A B C S : Type}
    {AS : Setoid A}
    {BS : Setoid B}
    {CS : Setoid C}
    {SS : Setoid S} : (AS ~~> shS SS BS) ~> (BS ~~> shS SS CS) ~~> (AS ~~> shS SS CS) := compM.

  Definition sh_plus {A B  S : Type}
    {AS : Setoid A}
    {BS : Setoid B}
    {SS : Setoid S}: (AS ~~> shS SS BS) ~> (AS ~~> shS SS BS) ~~> (AS ~~> shS SS BS) := mappend.

  Definition sh_zero {A B  S : Type}
    {AS : Setoid A}
    {BS : Setoid B}
    {SS : Setoid S}: AS ~> shS SS BS := mempty.

  Definition sh_one {A  S : Type}
    {AS : Setoid A}
    {SS : Setoid S}: AS ~> shS SS AS := ret.

  Context
    {A B C D S : Type}
    {AS : Setoid A}
    {BS : Setoid B}
    {CS : Setoid C}
    {DS : Setoid D}
    {SS : Setoid S}.

  (* category laws *)
  Lemma times_left_unit : forall a : AS ~> shS SS BS, sh_times @ sh_one @ a == a.
  Proof.
    intros. simpl. arrequiv.    
  Qed.
  
  Lemma times_right_unit : forall a : AS ~> shS SS BS, sh_times @ a @ sh_one == a.
  Proof.
    intros. unfold sh_times, sh_one. apply (@right_unit_comp (@sh S SS)).
  Qed.
  
  Lemma times_associativity : forall (a : AS ~> shS SS BS)  (b : BS ~> shS SS CS)  (c : CS ~> shS SS DS), sh_times @ (sh_times @ a @ b) @ c == sh_times @ a @ (sh_times @ b @ c).

  Proof.
    intros. apply (@associativity_comp (@sh S SS)).
  Qed.

  (* monoid-enriched category *)
  Lemma plus_left_unit : forall a : AS ~> shS SS BS, sh_plus @ sh_zero @ a == a.
  Proof.
    intros. apply left_unit_monoid.
  Qed.

  Lemma plus_right_unit : forall a : AS ~> shS SS BS, sh_plus @ a @ sh_zero == a.
  Proof.
    intros. apply right_unit_monoid.
  Qed.

  Lemma plus_associativity : forall (a b c: AS ~> shS SS BS), sh_plus @ (sh_plus @ a @ b) @ c == sh_plus @ a @ (sh_plus @ b @ c).
  Proof.
    intros. apply associativity_monoid.
  Qed.

  Lemma times_left_absorb :  forall a : AS ~> shS SS BS, sh_times @ sh_zero @ a == sh_zero.
  Proof.
    intros. simpl. arrequiv.
  Qed.
Set Printing Implicit.
  Lemma times_left_distributivity : forall (a b: AS ~> shS SS BS)  (c : BS ~> shS SS CS) , sh_times @ (sh_plus @ a @ b) @ c == sh_plus @ (sh_times @ a @ c) @ (sh_times @ b @ c).
  Proof.
    intros. unfold sh_times at 1. unfold sh_plus at 1. unfold compM, _compM. normalize. simpl_equiv. simpl mappend.  unfold arr_mappend. unfold comp3S, uncurryS, pairingF. normalize.  unfold fst, snd. rewrite (contT_left_distributivity SS (@storeHeapS) B C BS CS (a @ a0) (b @ a0) c).  reflexivity.
  Qed.
  

  (* Proof. *)

(*
  Instance sh_NearSemiRing : @NearSemiRing _ (SS ~~> shS SS).
  Proof.
    exists (@sh_one) (@sh_zero) (@sh_times) (@sh_plus).
  Defined.

*)
  
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
