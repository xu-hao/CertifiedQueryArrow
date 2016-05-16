Require Import Algebra.Functor Algebra.Applicative Algebra.SetoidCat Algebra.ListUtils Algebra.PairUtils Algebra.Maybe Algebra.SetoidUtils Algebra.Monad Algebra.Maybe Tactics Utils VectorUtils Algebra.Lens.LensTypes Algebra.Pointed Algebra.Lens.Lista Algebra.Lens.Matrixp Lens Algebra.Monoid.

Require Import SetoidClass List Coq.Classes.RelationClasses Coq.Arith.PeanoNat Coq.Arith.Compare_dec.

Definition _nthTraversal' {A} {AS : Setoid A} (n : nat) : _Traversal' (list A) A.
  unfold _Traversal'. intros. refine (match nth_error X0 n with
                                    | None => pure @ X0
                                    | Some a => listS_update n X0  X
                                  end).
Defined.

Definition _nthTraversal {f fS func} {app : @Applicative f fS func} {A} {AS : Setoid A} (n : nat) :
  (AS ~> fS _ AS) -> list A -> f (list A) _ := _nthTraversal' n f fS func app.

Instance _nthTraversal_Proper {f fS func} {app : @Applicative f fS func} A (AS : Setoid A) : Proper (equiv ==> equiv ==> equiv ==> equiv) (_nthTraversal).
Proof.
  autounfold. intros. unfold _nthTraversal, _nthTraversal'. matchequiv. rewrite H. clear x H. generalize y H1. clear y H1. apply list_ind_2 with (l1:=x1) (l2:=y1).
  intros. rewritesr. 
  intros. inversion H1.
  intros. inversion H1.
  intros. inversion H1. induction y.
  unfold listS_update. rewrite H0, H6, H8. reflexivity.
  unfold listS_update. fold listS_update. rewrite H. rewrite H6. reflexivity. auto. rewritesr.
Qed.

Definition nthTraversal {f fS func} {app : @Applicative f fS func} {A} {AS : Setoid A} := injF3 _nthTraversal _.



Definition _matrixColLens' {A} {AS : Setoid A} {AP : Pointed A} (n : nat) : _Lens' (matrixp A) (lista (maybe A)).
  unfold _Lens'. intros. refine (
                              updateMatrixCol @ n @
                                X0
                                <$> (X @ (readMatrixCol @ n @ X0))).
Defined.

Definition _matrixColLens {f fS }{func : @Functor f fS} {A} {AS : Setoid A} {AP : Pointed A} (n : nat) :
  (listaS (maybeS AS) ~> fS _ (listaS (maybeS AS))) -> matrixp A -> f (matrixp A) _ := _matrixColLens' n f fS func.

Instance _matrixColLens_Proper {f fS} {func : @Functor f fS} A (AS : Setoid A) (AP : Pointed A) : Proper (equiv ==> equiv ==> equiv ==> equiv) (_matrixColLens).
Proof.
  autounfold. intros. unfold _matrixColLens, _matrixColLens'. rewritesr. 
Qed.

Definition matrixColLens {f fS} {func : @Functor f fS} {A} {AS : Setoid A} {AP : Pointed A} := injF3 _matrixColLens _.



Definition _matrixWidthLens' {A : Type} {AS : Setoid A} {AP : Pointed A}  : _Lens' (matrixp A) nat.
  unfold _Lens'. intros. refine (flipS @ matrixpConsS @ (rows @ X0) <$> (X @ (width @ X0))).
Defined.

Definition _matrixWidthLens {f fS} {func : @Functor f fS} {A : Type} {AS : Setoid A} {AP : Pointed A}  :=
  @_matrixWidthLens' A AS AP f fS func.

Instance _matrixWidthLens_Proper {f fS} {func : @Functor f fS} {A : Type} {AS : Setoid A}{AP: Pointed A}: Proper (equiv ==> equiv ==> equiv ) (@_matrixWidthLens f fS func A AS AP).
Proof.
  autounfold. intros. unfold _matrixWidthLens, _matrixWidthLens'. rewritesr.
Qed.

Definition matrixWidthLens {f fS} {func : @Functor f fS} {A} {AS : Setoid A} {AP: Pointed A} :=
  injF2 (@_matrixWidthLens f fS func A AS AP ) _.

Definition _matrixRowsLens' {A : Type} {AS : Setoid A} {AP : Pointed A}  : _Lens' (matrixp A) (lista (maybe (lista A))).
  unfold _Lens'. intros. refine (matrixpConsS @ (width @ X0) <$> (X @ (rows @ X0))).
Defined.

Definition _matrixRowsLens {f fS} {func : @Functor f fS} {A : Type} {AS : Setoid A} {AP : Pointed A}  :=
  @_matrixRowsLens' A AS AP f fS func.

Instance _matrixRowsLens_Proper {f fS} {func : @Functor f fS} {A : Type} {AS : Setoid A} {AP : Pointed A} : Proper (equiv ==> equiv ==> equiv ) (@_matrixRowsLens f fS func A AS AP).
Proof.
  autounfold. intros. unfold _matrixRowsLens, _matrixRowsLens'. rewritesr.
Qed.

Definition matrixRowsLens {f fS} {func : @Functor f fS} {A} {AS : Setoid A} {AP : Pointed A}  :=
  injF2 (@_matrixRowsLens f fS func A AS AP ) _.

Require Import MaybeLens.
Definition matrixRowTraversal {f fS func} {app : @Applicative f fS func} {A} {AS : Setoid A} {AP : Pointed A}(n : nat) :=
  matrixRowsLens ∘ listaNthLens n ∘ maybePrism. 

Definition matrixCellTraversal {f fS func} {app : @Applicative f fS func} {A} {AS : Setoid A} {AP:Pointed A}(m n : nat) :=
  matrixRowTraversal m ∘ listaNthLens n.



Lemma listaNthLens_comp_view:
  forall (A : Type) (AS : Setoid A)
       B (BS : Setoid B) n (l : (BS ~~> ConstS BS BS) ~> AS ~~> ConstS BS AS),
    view (listaNthLens n ∘ l) == view l ∘ view (listaNthLens n).
Proof.
  intros. unfold view. simpl_equiv.  simpl. reflexivity.
Qed.

Lemma listaNthLens_comp_preview:
  forall (A : Type) (AS : Setoid A)
       B (BS : Setoid B) n (l : (BS ~~> ConstS (maybeS BS) BS) ~> AS ~~> ConstS (maybeS BS) AS),
    previewS @ (listaNthLens n ∘ l) == previewS @ l ∘ view (listaNthLens n).
Proof.
  intros. simpl_equiv. Opaque equiv.  simpl. Transparent equiv.  reflexivity.
Qed.

Lemma matrixRowsLens_comp_view:
  forall (A : Type) (AS : Setoid A) (AP :Pointed A)
       B (BS : Setoid B) (l : (BS ~~> ConstS BS BS) ~> listaS (maybeS (listaS AS)) ~~> ConstS BS (listaS (maybeS (listaS AS)))),
    view (matrixRowsLens ∘ l) == view l ∘ view (matrixRowsLens).
Proof.
  intros. simpl_equiv.  Opaque equiv. simpl. Transparent equiv. reflexivity.
Qed.

Lemma matrixRowsLens_comp_preview:
  forall (A : Type) (AS : Setoid A) (AP : Pointed A)
       B (BS : Setoid B) (l : (BS ~~> ConstS (maybeS BS) BS) ~> listaS (maybeS (listaS AS)) ~~> ConstS (maybeS BS) (listaS (maybeS (listaS AS)))),
    previewS @ (matrixRowsLens ∘ l) == previewS @ l ∘ view (matrixRowsLens).
Proof.
  intros. simpl_equiv. Opaque equiv.  simpl. Transparent equiv. reflexivity.
Qed.

Lemma listaNthLens_comp_set:
  forall (A : Type) (AS : Setoid A)
       B (BS : Setoid B) n (l : (BS ~~> IdentityS BS) ~> AS ~~> IdentityS AS) b h,
    set (listaNthLens n ∘ l) @ b @ h == set (listaNthLens n) @ ((set l @ b ∘ view (listaNthLens n)) @ h) @ h.
Proof.
  intros. unfold set, view. simpl_equiv.  simpl. reflexivity.
Qed.

Lemma listaNthLens_view_set:
  forall (A : Type) (AS : Setoid A)
       n  h,
    set (listaNthLens n) @ (view (listaNthLens n) @ h) @ h == h.
Proof.
  intros. simpl. destruct h. apply nat_list_ind_2 with (l1:=n) (l2:=l).
  - simpl. split.  reflexivity. split.  reflexivity. auto.
  - intros. simpl. split. reflexivity. fold (lista_equiv (listaCons _ a b) (listaCons _ a b)). reflexivity.
  - intros. simpl. split. reflexivity. simpl in H. destruct b; [auto|auto].
  - intros. simpl. split. reflexivity. auto. 
Qed.

Lemma matrixRowsLens_comp_set:
  forall (A : Type) (AS : Setoid A) (AP :Pointed A)
       B (BS : Setoid B) (l : (BS ~~> IdentityS BS) ~> listaS (maybeS (listaS AS)) ~~> IdentityS (listaS (maybeS (listaS AS)))) b h,
    set (matrixRowsLens ∘ l) @ b @ h == set (matrixRowsLens) @ ((set l @ b ∘ view (matrixRowsLens)) @ h) @ h.
Proof.
  intros. Opaque equiv. simpl. Transparent equiv. reflexivity.
Qed.

Lemma truncate_idempotent:
  forall A (AS : Setoid A) n a (l : lista A),
    lista_truncate n a (lista_truncate n a l) == lista_truncate n a l.
Proof.
  intros. destruct l. apply nat_list_ind_2 with (l1:=n) (l2:=l).
  - reflexivity.
  - intros. simpl. split. reflexivity. auto.
  -    intros. simpl. split. reflexivity. auto.
  -    intros. split. reflexivity    . auto.
Qed.

Lemma matrixRowsLens_view_set:
  forall (A : Type) (AS : Setoid A) (AP :Pointed A) h,
    set matrixRowsLens @ (view matrixRowsLens @ h) @ h == h.
Proof.
  intros. Opaque equiv. simpl. destruct h. destruct l. split. reflexivity. unfold _rows. simpl (_width (matrixpCons A n (listaCons (option (lista A)) o l))). induction l.
  - split.
    + destruct o.
    * Transparent equiv. simpl. apply truncate_idempotent.
    *  reflexivity.
    + simpl.  auto.
  - split.
    + destruct a.
      * simpl. apply truncate_idempotent.
      * reflexivity.
    + simpl. auto.
Qed.

Existing Instance maybe_first_Monoid.
Lemma right_unit_monoid_maybe :
  forall (A : Type) (AS : Setoid A) (a : A),
    mappend @ Some a @ mempty = Some a.
Proof.
  intros. simpl. auto.
Qed.

Opaque equiv mappend mempty. 

Definition ConstCastS {A B C} (CS : Setoid C) (AS : Setoid A) (BS : Setoid B) : ConstS CS AS ~> ConstS CS BS := ConstIsoS _ _ ∘ ConstIsoS' _ _. 

Lemma nthTraversal_cons_O :
  forall A (AS : Setoid A) (a : A) (l : list A) f fS func (app : @Applicative f fS func)
         (g : AS ~> fS _ AS),
    nthTraversal @ 0 @ g @ (a :: l) == consS <$> g @ a <*> pure @ l.
Proof.
  intros. reflexivity. 
Qed.

Lemma nthTraversal_cons_S :
  forall A (AS : Setoid A) n (a : A) (l : list A) f fS func (app : @Applicative f fS func)
  (g : AS ~> fS _ AS),
    nthTraversal @ (S n) @ g @ (a :: l) == consS @ a <$> nthTraversal @ n @ g @ l.
Proof.
  intros. Opaque consS.  simpl. unfold _nthTraversal, _nthTraversal'. simpl (nth_error _ _).  destruct (nth_error l n).
  - Opaque uncurryS constS. simpl. generalize (listS_update n l g). intros.  rewrite fmap_fmap. rewrite <- (fmap_idS_absorb f0) at 1. rewrite naturality_prod. rewrite <- (left_unit_applicative f0) at 2. rewrite fmap_fmap. rewrite fmap_fmap. evalproper. evalproper. Transparent consS uncurryS constS equiv.  simpl_equiv. simpl.  destruct a1. simpl. reflexivity.
  - simpl. rewrite fmap_fmap. evalproper. evalproper. simpl. arrequiv. 
Qed.

Lemma nthTraversal_cons_O_Const :
  forall A (AS : Setoid A) (a : A) (l : list A) B (BS : Setoid B) (BM : @Monoid B BS)  
  (g : AS ~> ConstS BS AS),
    nthTraversal @ 0 @ g @ (a :: l) == ConstCastS _ _ _ @ (g @ a).
Proof.
  intros. rewrite nthTraversal_cons_O.  simpl.  rewrite right_unit_monoid. reflexivity.
Qed.

Lemma nthTraversal_cons_S_Const :
  forall A (AS : Setoid A) n (a : A) (l : list A) B (BS : Setoid B) (BM : @Monoid B BS)
  (g : AS ~> ConstS BS AS),
    nthTraversal @ (S n) @ g @ (a :: l) == nthTraversal @ n @ g @ l.
Proof.
  intros. rewrite nthTraversal_cons_S. Opaque ConstIsoS ConstIsoS' equiv. simpl.  rewrite ConstIsoS'_iso. reflexivity.
Qed.

Lemma nthTraversal_cons_O_Identity :
  forall A (AS : Setoid A) (a : A) (l : list A)
  (g : AS ~> IdentityS AS),
    nthTraversal @ 0 @ g @ (a :: l) == IdentityIsoS _ @ (IdentityIsoS' _ @ (g @ a) :: l).
Proof.
  intros. rewrite nthTraversal_cons_O.  simpl.  reflexivity.
Qed.

Lemma nthTraversal_cons_S_Identity :
  forall A (AS : Setoid A) n (a : A) (l : list A)
  (g : AS ~> IdentityS AS),
    nthTraversal @ (S n) @ g @ (a :: l) == IdentityIsoS _ @ (a :: IdentityIsoS' _ @ (nthTraversal @ n @ g @ l)).
Proof.
  intros. rewrite nthTraversal_cons_S. simpl.  reflexivity.
Qed.

Opaque nthTraversal.

Lemma nthTraversal_comp_preview:
  forall (A : Type) (AS : Setoid A)
       B (BS : Setoid B) n (l : (BS ~~> ConstS (maybeS BS) BS) ~> AS ~~> ConstS (maybeS BS) AS),
    previewS @ (nthTraversal @ n ∘ l) == previewS @ (nthTraversal @ n) >=> previewS @ l.
Proof.
  intros. Transparent equiv. simpl_equiv. Opaque equiv. generalize n. clear n. induction a. 
  - intros. Opaque equiv. simpl. unfold _nthTraversal, _nthTraversal', _pre0. destruct n.
    + simpl. reflexivity.
    + simpl. reflexivity. 
  - intros.   destruct n.
    +  Opaque ConstIsoS ConstIsoS' caseMaybeS pre0. simpl. rewrite nthTraversal_cons_O_Const. pose (nthTraversal_cons_O_Const _ _ a a0 _ _ _ (pre0 @ ConstIsoS (maybeS AS) (maybeS AS))) as e.  rewrite e. clear e. Transparent pre0. simpl. unfold _pre0. simpl. rewrite ConstIsoS_iso. rewrite ConstIsoS_iso. rewrite ConstIsoS_iso. unfold ConstMaybeIsoS'. rewrite (ConstIsoS_iso _ _ _ _ (Some a)). Transparent caseMaybeS. simpl. evalproper.
    +  Opaque ConstIsoS ConstIsoS' caseMaybeS pre0. simpl. rewrite nthTraversal_cons_S. pose (nthTraversal_cons_S_Const _ _ n a a0 _ _ _ (pre0 @ ConstIsoS (maybeS AS) (maybeS AS))) as e.  rewrite e. clear e. apply IHa.
       Transparent ConstIsoS ConstIsoS' caseMaybeS pre0. 
Qed.
Transparent nthTraversal.
Lemma IdentityS_iso : forall (A : Type) (AS : Setoid A) (a : A), IdentityIsoS' _ @ (IdentityIsoS _ @ a) = a.
Proof.
  reflexivity.
Qed.
Section nthTraversal_preview_set.
Lemma nthTraversal_preview_set:
  forall (A : Type) (AS : Setoid A) n b a,
    (previewS @ (nthTraversal @ n) @ a) == Some b
    \/ (previewS @ (nthTraversal @ n) @ a) == None ->
    set (nthTraversal @ n) @ b @ a == a.
Proof.
  intros. Opaque equiv. generalize H.  clear H. apply nat_list_ind_2 with (l1:=n) (l2:=a). 
  - intros. simpl. reflexivity.
  - intros. destruct H0. simpl in *.  rewrite right_unit_monoid in H0. Transparent equiv. simpl in H0. rewrite H0. reflexivity.
    inversion H0. 
  - intros. simpl. reflexivity.
  - intros. unfold set. unfold flipS. normalizecomp. unfold compS. normalizecomp. rewrite nthTraversal_cons_S_Identity. rewrite IdentityS_iso. constructor. reflexivity.
    apply H. clear H.    destruct H0.
    left. Opaque nthTraversal ConstIsoS' equiv pre0. simpl in *. rewrite (nthTraversal_cons_S_Const   A AS b0 c d (maybe A) (maybeS AS) (@maybe_first_Monoid A AS) (pre0 @ ConstIsoS (maybeS AS) (maybeS AS))) in H. auto.
    right. Opaque nthTraversal ConstIsoS' equiv pre0. simpl in *. rewrite (nthTraversal_cons_S_Const   A AS b0 c d (maybe A) (maybeS AS) (@maybe_first_Monoid A AS) (pre0 @ ConstIsoS (maybeS AS) (maybeS AS))) in H. auto.
Qed.
End nthTraversal_preview_set.

Lemma nthTraversal_set:
  forall (A : Type) (AS : Setoid A)
         B (BS : Setoid B) n (l : (BS ~~> IdentityS BS) ~> AS ~~> IdentityS AS) b a,
    set (nthTraversal @ n ∘ l) @ b @ a == caseMaybeS
                                            @ (flipS @ set (nthTraversal @ n) @ a ∘ set l @ b)
                                            @ a
                                            @ (previewS @ (nthTraversal @ n) @ a).
Proof.
  intros. Opaque equiv. apply nat_list_ind_2 with (l1:=n) (l2:=a). 
  - intros. simpl. reflexivity.
  - intros. simpl.  rewrite right_unit_monoid. simpl. reflexivity. 
  - intros. simpl. reflexivity.
  - intros. unfold set at 1. unfold flipS at 1 2. unfold comp at 1 2 3 4. normalize. unfold compS. unfold comp at 1. normalize. rewrite nthTraversal_cons_S_Identity. rewrite IdentityS_iso.
    assert (previewS @ (nthTraversal @ S b0) @ (c :: d) == previewS @ (nthTraversal @ b0) @ ( d)).
    Opaque nthTraversal ConstIsoS' pre0. simpl.  rewrite (nthTraversal_cons_S_Const A AS b0 c d (maybe A) (maybeS AS) (@maybe_first_Monoid A AS) (pre0 @ ConstIsoS (maybeS AS) (maybeS AS))). reflexivity.
    rewrite H0.
    rewrite H. destruct (previewS @ (nthTraversal @ b0) @ d).
    + unfold caseMaybeS, caseMaybe, flipS. normalizecomp. unfold set at 3. unfold flipS, compS, comp. normalize. rewrite nthTraversal_cons_S_Identity. rewrite IdentityS_iso. reflexivity.
    + reflexivity.
Qed.

  Lemma listaNthLens_preview_view : forall A (AS : Setoid A) n (a : lista A), (previewS @ listaNthLens n @ a) == Some (view (listaNthLens n) @ a).
  Proof.
    intros. reflexivity.
  Qed.

