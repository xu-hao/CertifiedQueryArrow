Require Import Assert Command Algebra.Utils.
Require Import Coq.Lists.List PeanoNat.

Inductive spec :=
| partial : assertion -> command -> assertion -> spec
.

Notation "{{ a }} b {{ c }}" := (partial a b c) (at level 88).

Module Spec (B : BuiltInExpr) (BP : BuiltInPred) (S : Store) (H: Heap).
  Module SEM := Semantics B BP S H.
  Module M := Models B S H.
  Import S M SEM.
  Definition models s h spec : Prop :=
    match spec with
      | partial a comm a2 =>
        let (s's, h') := reduce comm s h in
        ⟦ a ⟧ s h ->
        fold_right and True (map (fun s => ⟦ a2 ⟧ s h') s's)
    end
  .
  Notation "s ; h ⊢ spec" := (models s h spec) (at level 89).
  Notation "⊢ spec" := (forall s h, s ; h ⊢ spec) (at level 89).
  
  Lemma consequence :
    forall p p' q q' c, p' ⇒ p -> ⊢ {{ p }} c {{ q }} -> q ⇒ q' -> ⊢ {{ p' }} c {{ q' }}.
  Proof.
    intros. unfold models in *. pose (H0sh := H0 s h). extract_common (reduce c s h). clear H0 x. intro. assert (fold_right and True (map (fun s : S.t => (⟦ q ⟧) s t0) l)). apply (H0sh (H s h H0)). clear H0 H0sh h s p p' c H. induction l.
      + simpl in *. apply H2.
      + simpl in *. destruct H2. split.
        - apply H1. apply H.
        - apply IHl. apply H0.
  Qed.

  Lemma aux_var_elim :
    forall p q v c,
      ⊢ {{ p }} c {{ q }} ->
      ~ (v ∈ cFreeVars c) ->
      ⊢ {{ aexists v, p }} c {{ aexists v, q }}.
  Proof.
    intros. unfold models in *.  rewrite let_intro. intro. destruct H1.
    assert (let (s's, h') := reduce c (s [v ↦ x ]s) h in
      (⟦ p ⟧) (s [v ↦ x ]s) h ->
      fold_right and True (map (fun s0 : t => (⟦ q ⟧) s0 h') s's)) as Hsh. apply (H (s [v ↦ x ]s) h).
    clear H. rewrite let_intro in Hsh. 
    assert (
      fold_right and True
          (map (fun s0 : t => (⟦ q ⟧) s0 (snd (reduce c (s [v ↦ x ]s) h)))
               (fst (reduce c (s [v ↦ x ]s) h)))). auto. clear Hsh H1. destruct (comm_store_non_interference_2 v c s h x H0). rewrite <- H2 in H. rewrite <- H1 in H. clear H1 H2. destruct (reduce c s h). simpl in *. induction l.
    * auto.
    * simpl. destruct H. split.
      + exists x. auto.
      + auto.
  Qed.


  
End Spec.
