Require Import Algebra.Functor Algebra.Applicative Algebra.SetoidCat Algebra.ListUtils Algebra.PairUtils Algebra.Maybe Algebra.SetoidUtils Algebra.Monad LensTypes Tactics Utils Monoid MonoidUtils.
Require Import SetoidClass List.


Existing Instance ConstS.

Section Settable.

  Context
    {A B}
    {AS : Setoid A}
    {BS : Setoid B}
    {t}
    {tS : Setoid t}.
  
  Class Settable :=
    {
      set : tS ~> BS ~~> AS ~~> AS;
    }.

End Settable.

Section PreLens.

  Context
    {A B}
    {AS : Setoid A}
    {BS : Setoid B}
    {t}
    {tS : Setoid t}
    {sett : @Settable A B AS BS t tS}.
  
  Class PreLens :=
    {
      view : tS ~> AS ~~> BS;
      set_view: forall l a, set @ l @ (view @ l @ a) @ a == a    
    }.

End PreLens.

Section Preview.

  Context
    {A B}
    {AS : Setoid A}
    {BS : Setoid B}
    {t}
    {tS : Setoid t}
    {sett : @Settable A B AS BS t tS}.
  
  Class Preview  :=
    {
      preview : tS ~> AS ~~> maybeS BS;
      preview_set_Some : forall l a b b2, preview @ l @ a == Some b2 ->
                                          preview @ l @ (set @ l @ b @ a) == Some b;
      preview_set_None : forall l a b, preview @ l @ a == None ->
                                          preview @ l @ (set @ l @ b @ a) == None;
      set_preview_Some: forall l a b, preview @ l @ a == Some b ->
                                      set @ l @ b @ a == a;
      set_preview_None: forall l a b, preview @ l @ a == None ->
                                      set @ l @ b @ a == a
    }.

  Definition _pset_set (ps : tS ~> BS ~~> AS ~~> AS) (l: t) (b: maybe B) (a: A) : A :=
    caseMaybeS
      @ (cycle23S @ ps @ l @ a)
      @ a
      @ b.

  Instance _pset_set_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) _pset_set.
  Proof.
    solve_properS _pset_set.
  Qed.

  Definition pset_set := injF4 _pset_set _.
  
  Instance Preview_Maybe_Settable (prv : Preview) : @Settable A (maybe B) _ _ t tS.
  Proof.
    split.
    exact (pset_set @ set).
  Defined.
  
  Instance Preview_PreLens (prv : Preview) : @PreLens A (maybe B) _ _ t tS _.
  Proof.
    exists (preview) .
    intros. simpl. unfold _pset_set. simpl. unfold caseMaybe. simpl. destruct (maybe_case (preview @ l @ a)).
    - rewrite H. reflexivity.
    - destruct H. rewrite H. apply set_preview_Some. rewrite H. reflexivity.
  Defined.
   
End Preview.

Section Lens.

  Context
    {A B}
    {AS : Setoid A}
    {BS : Setoid B}
    {t}
    {tS : Setoid t}
    {sett}
    {pl : @PreLens A B AS BS t tS sett}.
  
  Class Lens :=
    {
      set_set : forall (l : t) (a : A) (b1 b2 : B), set @ l @ b2 @ (set @ l @ b1 @ a) == set @ l @ b2 @ a;
      view_set : forall (l : t) (a : A) (b : B), view @ l @ (set @ l @ b @ a) == b
    }.

  Definition Lens_preview : tS ~> AS ~~> maybeS BS := comp2S @ view @ SomeS.
  Instance Lens_Preview (ls : Lens) : @Preview A B AS BS t tS sett.
  Proof.
    exists (Lens_preview).
    intros. simpl in *. rewrite view_set. reflexivity.
    intros. simpl in *. auto.
    intros. simpl in *. rewrite <- H. rewrite set_view. reflexivity.
    intros. simpl in *. tauto.
  Defined.
  

End Lens.




Section ComposePreLens.
  Context
    {A B C}
    {AS : Setoid A}
    {BS : Setoid B}
    {CS : Setoid C}
    {t}
    {tS : Setoid t}
    {sett}
    {pl : @PreLens A B AS BS t tS sett}
    {t2}
    {t2S : Setoid t2}
    {sett2}
    {pl2 : @PreLens B C BS CS t2 t2S sett2}.
  
  Inductive ComposeL := ComposeLIso : t -> t2 -> ComposeL.

  Definition ComposeL_equiv l l' :=
    match l, l' with
      | ComposeLIso l1 l2, ComposeLIso l1' l2' => l1 == l1' /\ l2 == l2'
    end. 

  Instance ComposeL_equiv_Equivalence : Equivalence ComposeL_equiv.
  Proof.
    split.
    autounfold. intros. destruct x.  simpl.  split; [reflexivity | reflexivity].
    autounfold. intros. destruct x, y. destruct H. split; [symmetry ; auto | symmetry ; auto].
    autounfold. intros. destruct x, y, z. destruct H, H0. split; [transitivity t3; [auto | auto] | transitivity t4; [auto | auto]].
  Qed.

  Instance ComposeLS : Setoid ComposeL :=
    {
      equiv := ComposeL_equiv
    }
  .
  
  Definition _ComposeL_view l : AS ~> CS :=
    match l with
      | ComposeLIso l1 l2 => view @ l2 ∘ view @ l1
    end.

  Instance _ComposeL_view_Proper : Proper (equiv ==> equiv) _ComposeL_view.
  Proof.
    autounfold. intros. destruct x,y. destruct H. simpl. arrequiv. rewritesr.
  Qed.

  Definition ComposeL_view : ComposeLS ~> AS ~~> CS := injF _ComposeL_view _.

  Definition _ComposeL_set l (c : C) (a : A) : A :=
    match l with
      | ComposeLIso l1 l2 => set @ l1 @ (set @ l2 @ c @ (view @ l1 @ a)) @ a
    end.

  Instance _ComposeL_set_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _ComposeL_set.
  Proof.
    autounfold. intros. destruct x, y. destruct H. simpl. rewritesr.
  Qed.

  Definition ComposeL_set := injF3 _ComposeL_set _.

  Instance ComposeL_Settable : @Settable A C AS CS ComposeL ComposeLS.
  Proof.
    split.
    exact ComposeL_set.
  Defined.
  
  Instance ComposeL_PreLens : @PreLens A C AS CS ComposeL ComposeLS _.
  Proof.
    exists ComposeL_view .
    intros. destruct l. simpl. rewrite set_view. rewrite set_view. reflexivity.
  Defined.

End ComposePreLens.

Section ComposePreview.
  Context
    {A B C}
    {AS : Setoid A}
    {BS : Setoid B}
    {CS : Setoid C}
    {t}
    {tS : Setoid t}
    {sett}
    {prv : @Preview A B AS BS t tS sett}
    {t2}
    {t2S : Setoid t2}
    {sett2}
    {prv2 : @Preview B C BS CS t2 t2S sett2}.

  Inductive ComposeP := ComposePIso : t -> t2 -> ComposeP.

  Definition ComposeP_equiv l l' :=
    match l, l' with
      | ComposePIso l1 l2, ComposePIso l1' l2' => l1 == l1' /\ l2 == l2'
    end. 

  Instance ComposeP_equiv_Equivalence : Equivalence ComposeP_equiv.
  Proof.
    split.
    autounfold. intros. destruct x.  simpl.  split; [reflexivity | reflexivity].
    autounfold. intros. destruct x, y. destruct H. split; [symmetry ; auto | symmetry ; auto].
    autounfold. intros. destruct x, y, z. destruct H, H0. split; [transitivity t3; [auto | auto] | transitivity t4; [auto | auto]].
  Qed.

  Instance ComposePS : Setoid ComposeP :=
    {
      equiv := ComposeP_equiv
    }
  .
  
  Definition _ComposeP_preview (l :ComposeP ) (a : A) : maybe C :=
    match l with
      | ComposePIso l1 l2 =>
        caseMaybeS
          @ (preview @ l2)
          @ None
          @ (preview @ l1 @ a)
    end.

  Instance _ComposeP_preview_Proper : Proper (equiv ==> equiv ==> equiv) _ComposeP_preview.
  Proof.
    autounfold. intros. destruct x,y. destruct H. unfold _ComposeP_preview.   rewritesr.
  Qed.

  Definition ComposeP_preview := injF2 _ComposeP_preview _.
  
  Definition _ComposeP_Preview_set (l : ComposeP) (c : C) (a : A) : A :=
    match l with
      | ComposePIso l1 l2 =>
        caseMaybeS
          @ (flipS @ (set @ l1) @ a ∘ set @ l2 @ c)
          @ a
          @ (preview @ l1 @ a)
    end.

  Instance _ComposeP_Preview_set_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _ComposeP_Preview_set.
  Proof.
    autounfold. intros. destruct x,y. destruct H. unfold _ComposeP_Preview_set. rewritesr.
  Qed.

  Definition ComposeP_Preview_set : (ComposePS) ~> CS ~~> AS ~~> AS := injF3 _ComposeP_Preview_set _.

  Instance ComposeP_Settable : @Settable A C AS CS (ComposeP) (ComposePS).
  Proof.
    split.
    exact ComposeP_Preview_set.
  Defined.
  
  Instance ComposeP_Preview : @Preview A C AS CS (ComposeP) (ComposePS) _.
  Proof.    
    exists ComposeP_preview.
    - intros. destruct l. unfold ComposeP_preview, _ComposeP_preview in *. normalize. unfold injF2 in H. repeat rewrite eval_injF in H. destruct (maybe_case (preview @ t0 @ a)).
      + rewrite H0 in H. simpl in H. tauto.
      + destruct H0. rewrite H0 in *. simpl set.  unfold ComposeP_Preview_set, _ComposeP_Preview_set. normalize. rewrite H0. simpl ((caseMaybeS @ (flipS @ (set @ t0) @ a ∘ set @ t1 @ b) @ a @ Some x)). rewrite @preview_set_Some with (b2:=x); [| rewrite H0; reflexivity]. Opaque equiv. simpl in *. destruct (maybe_case (preview @ t1 @ x)).
        *   rewrite H1 in H. inversion H.
        * destruct H1. apply @preview_set_Some with (b2:=x0). rewrite H1. reflexivity.
    - intros. destruct l. simpl in *. destruct (maybe_case (preview @ t0 @ a)).
      + rewrite H0 in *. simpl in *. rewrite H0. reflexivity.
      + destruct H0. rewrite H0 in *. simpl in *. rewrite @preview_set_Some with (b2:=x); [| rewrite H0; reflexivity]. simpl. apply preview_set_None. auto.
    - intros. destruct l. simpl in *. destruct (maybe_case (preview @ t0 @ a)).
      + rewrite H0 in *. simpl in *. reflexivity.
      + destruct H0. rewrite H0 in *. simpl in *. rewrite set_preview_Some. reflexivity. rewrite H0. rewrite set_preview_Some. reflexivity. auto.
    - intros. destruct l. simpl in *. destruct (maybe_case (preview @ t0 @ a)).
      + rewrite H0 in *. simpl in *. reflexivity.
      + destruct H0. rewrite H0 in *. simpl in *. rewrite set_preview_Some. reflexivity. rewrite H0. rewrite set_preview_None. reflexivity. auto.
  Defined.
  
End ComposePreview.

Section ComposeLens.
  Context
    {A B C}
    {AS : Setoid A}
    {BS : Setoid B}
    {CS : Setoid C}
    {t}
    {tS : Setoid t}
    {sett pl }
    {ls : @Lens A B AS BS t tS sett pl}
    {t2}
    {t2S : Setoid t2}
    {sett2 pl2}
    {ls2 : @Lens B C BS CS t2 t2S sett2 pl2}.

  Existing Instance ComposeL_Settable.
  Existing Instance ComposeL_PreLens.
  Instance ComposeL_Lens : @Lens A C AS CS (@ComposeL t t2) (@ComposeLS t tS t2 t2S) _ _.
  Proof.
    split.
    intros. destruct l. simpl. rewrite set_set. rewrite view_set. rewrite set_set. reflexivity.
    intros. destruct l. simpl. rewrite view_set. rewrite view_set. reflexivity.
  Qed.

End ComposeLens.

Notation "a >>> b" := (ComposeLIso a b) (at level 45, left associativity).
Notation "a >>>? b" := (ComposePIso a b) (at level 45, left associativity).

Existing Instance ComposePS.
Existing Instance ComposeP_Preview.
Existing Instance ComposeP_Settable.
Existing Instance maybe_Monad.

Lemma preview_comp :
  forall {A} {B} {C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C} {t tS sett} 
         {prv : @Preview A B AS BS t tS sett}
         {t2 t2S sett2}
         {prv2 : @Preview B C BS CS t2 t2S sett2} (l : t) (l2 : t2),
    preview @ (l >>>? l2) == preview @ l >=> (preview @ l2 : BS ~> maybeS CS).
Proof.
  intros. simpl. arrequiv. 
Qed.

