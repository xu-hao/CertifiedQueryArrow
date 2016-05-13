Require Import Algebra.Functor Algebra.Applicative Algebra.SetoidCat Algebra.ListUtils Algebra.PairUtils Algebra.Maybe Algebra.SetoidUtils Algebra.Monad LensTypes MaybeLens Tactics Utils Monoid MonoidUtils.
Require Import SetoidClass List.


Existing Instance ConstS.

Definition view {A} {B} {AS : Setoid A} {BS : Setoid B} (l : (BS ~~> ConstS BS BS) ~> (AS ~~> ConstS BS AS)) : AS ~> BS := ConstIsoS' _ _ ∘ (l @ ConstIsoS _ _).

Instance view_Proper {A} {B} {AS : Setoid A} {BS : Setoid B} : Proper (equiv ==> equiv) (@view A B _ _).
Proof.
  autounfold. intros. unfold view. rewritesr.
Qed.

Definition viewS {A} {B} {AS : Setoid A} {BS : Setoid B} := injF (@view A B _ _) _.

Definition set {A} {B} {AS : Setoid A} {BS : Setoid B} (l : (BS ~~> IdentityS BS) ~> (AS ~~> IdentityS AS)) : BS ~> AS ~~> AS :=  (flipS @ compS @ IdentityIsoS' _) ∘ l ∘ (flipS @ compS @ IdentityIsoS BS ∘ constS BS).

Instance set_Proper {A} {B} {AS : Setoid A} {BS : Setoid B} : Proper (equiv ==> equiv) (@set A B _ _).
Proof.
  autounfold. intros. unfold set. rewritesr.
Qed.

Definition setS {A} {B} {AS : Setoid A} {BS : Setoid B} := injF (@set A B _ _) _.

Existing Instance nat_Monoid.
Existing Instance ConstFunctor.
Existing Instance Const_Applicative.
Existing Instance ConstS.
Existing Instance maybe_Monad.
Existing Instance monadFunctor.
Existing Instance monad_Applicative.
Existing Instance IdentityS.
Existing Instance IdentityFunctor.
Existing Instance Identity_Applicative.



Definition ConstMaybe C {CS : Setoid C} A {AS : Setoid A} := ConstFunc (maybe C) A.
Instance ConstMaybeS {C} (CS : Setoid C) {A} (AS : Setoid A) : Setoid (ConstMaybe C A) :=
  ConstS (maybeS CS) AS.

Instance ConstMaybeFunctor {C} {CS : Setoid C} : @Functor (ConstMaybe C) _ := ConstFunctor (maybe C) _.


Definition _maybe_first_mappend {C} {CS : Setoid C}  (a b : maybe C) : maybe C :=
  match a with
    | None => b
    | Some a' => a
  end
.

Instance _maybe_first_mappend_Proper {C} {CS : Setoid C}  : Proper (equiv ==> equiv ==> equiv) _maybe_first_mappend.
Proof.
  autounfold. intros. unfold _maybe_first_mappend. matchequiv. auto. auto. 
Qed.

Definition maybe_first_mappend {C} {CS : Setoid C} : maybeS CS ~> maybeS CS ~~> maybeS CS := injF2 _maybe_first_mappend _.
      
Instance maybe_first_Monoid {C} {CS : Setoid C} : @Monoid (maybe C) _.
Proof.
  exists (None) (maybe_first_mappend).
  intros. simpl. destruct a. reflexivity. auto.
  intros. destruct a. simpl. reflexivity. simpl. auto.
  intros. destruct a. simpl. reflexivity. destruct b. simpl. reflexivity. simpl. destruct c.  reflexivity.  auto.
Defined.

Instance ConstMaybe_Applicative {C} {CS : Setoid C}  : @Applicative (ConstMaybe C) _ _ := Const_Applicative.
      
Definition ConstMaybeIsoS' {C} (CS : Setoid C) {A} (AS : Setoid A) : ConstMaybeS CS AS ~> maybeS CS :=
  ConstIsoS' (maybeS CS) AS.

Definition _pre0 {B} {BS : Setoid B} (f : maybeS BS ~> ConstS (maybeS BS) (maybeS BS)) ( a : B) : ConstMaybe B B := ConstIsoS _ _ @ (ConstMaybeIsoS' _ _ @ (f @ (SomeS @ a))).

Instance _pre0_Proper {B} {BS : Setoid B} : Proper (equiv ==> equiv ==> equiv) _pre0.
Proof.
  autounfold. intros. unfold _pre0. rewritesr. 
Qed.

Definition pre0 {B} {BS : Setoid B} := injF2 _pre0 _.
    
(* Definition _pre1 {A B} {AS : Setoid A} {BS : Setoid B} (f : AS ~> ConstMaybeS BS AS) ( a : A) : ConstMaybe (maybe B) A := ConstIsoS _ _ @ (ConstMaybeIsoS' _ _ @ (f @ a)).

Instance _pre1_Proper {A B} {AS : Setoid A} {BS : Setoid B} : Proper (equiv ==> equiv ==> equiv) _pre1.
Proof.
  autounfold. intros. unfold _pre1. rewritesr. 
Qed.

Definition pre1 {A B} {AS : Setoid A} {BS : Setoid B} := injF2 _pre0 _. *)
    
Definition pre {A} {B} {AS : Setoid A} {BS : Setoid B} (l : (BS ~~> ConstMaybeS BS BS) ~> (AS ~~> ConstMaybeS BS AS)) : (maybeS BS ~~> ConstS (maybeS BS) (maybeS BS)) ~> (AS ~~> ConstS (maybeS BS) AS)
  :=
  l ∘ pre0.

Instance pre_Proper {A} {B} {AS : Setoid A} {BS : Setoid B} : Proper (equiv ==> equiv) (@pre A B _ _).
Proof.
  autounfold. intros. unfold pre. rewritesr.
Qed.

Definition preS {A} {B} {AS : Setoid A} {BS : Setoid B} := injF (@pre A B _ _) _.

Definition previewS {A} {B} {AS : Setoid A} {BS : Setoid B} : ((BS ~~> ConstMaybeS BS BS) ~~> (AS ~~> ConstMaybeS BS AS)) ~> AS ~~> maybeS BS := viewS ∘ preS.


(*
Definition lens_iso {A B} {AS : Setoid A} {BS : Setoid B}
           (l : forall f fS (func : @Functor f fS), (BS ~~> fS _ BS) ~> (AS ~~> fS _ AS)) :
  AS ~> BS ~*~ (BS ~~> AS) :=
  viewS @ l _ _ _ &&& flipS @ (setS @ l _ _ _). 
  
Definition _lens_iso' {A B} {AS : Setoid A} {BS : Setoid B}
           (l : AS ~> BS ~*~ (BS ~~> AS)) f fS (func : @Functor f fS) (g : BS ~> fS _ BS) (a : A) : f A _ :=
  match l @ a with
    | (v, s) => s <$> g @ v
  end.

Instance _lens_iso'_Proper  {A B} {AS : Setoid A} {BS : Setoid B} (l : AS ~> BS ~*~ (BS ~~> AS)) {f fS} {func : @Functor f fS}: Proper (equiv ==> equiv ==> equiv) (_lens_iso' l _ _ _).
Proof.
  autounfold. intros. unfold _lens_iso'. simpl_let. rewritesr.
Qed.

Definition lens_iso' {A B} {AS : Setoid A} {BS : Setoid B}
           (l : AS ~> BS ~*~ (BS ~~> AS)) f fS (func : @Functor f fS) := injF2 (_lens_iso' l _ _ _) _.



view l =(fun a => l id a).
set l = (fun a b => l (const b) a).
v = l id a.
s = (fun b => l (const b) a).


Hom(Hom(A, -), G) ~ G A

Hom(Hom(F, ~), 
flip l a <$> (const <$> g (l id a)) == l g a.

          
(l . const <$> g (l id)) == l g 
Lemma lens_iso_iso_1 :
  forall {A B} {AS : Setoid A} {BS : Setoid B}
         (l : forall f fS (func : @Functor f fS), (BS ~~> fS _ BS) ~> (AS ~~> fS _ AS))
         f fS (func : @Functor f fS),
    lens_iso' (lens_iso l) f fS func == l f fS func.
Proof.
  intros. simpl. arrequiv. unfold lens_iso, lens_iso', _lens_iso', pairingF. normalize. unfold viewS, view, setS, set. unfold flipS. simpl. normalizecomp. simpl.


  
Lemma flip_lens :
  forall {A B} {AS : Setoid A} {BS : Setoid B} {f fS} {func : @Functor f fS}
         (l : forall {f fS} {func : @Functor f fS}, (BS ~~> fS _ BS) ~> (AS ~~> fS _ AS))
         (f : (BS ~> fS _ BS))
         (a : A),
    l @ f @ a =  flipped_lens (@l) a @ f.
Proof.
  reflexivity. 
Qed.

Existing Instance comp_Proper.

Lemma view_comp :
  forall {A} {B} {C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C}
         (l : forall {f fS} {func : @Functor f fS}, (BS ~~> fS _ BS) ~> (AS ~~> fS _ AS))
         (l2 : forall {f fS} {func : @Functor f fS}, (CS ~~> fS _ CS) ~> (BS ~~> fS _ BS)),
    view (l ∘ l2) == view l2 ∘ view l.
Proof.
  intros. unfold view at 1. normalizecomp.  rewrite (flip_lens l). rewrite (flip_lens l). rewrite flip_lens. rewrite flip_lens. unfold comp at 3. unfold eval. repeat rewrite projF_injF. setoid_rewrite eval_injF. normalize. 

Lemma comp_id : forall {A B} {AS : Setoid A} {BS : Setoid B} (f : AS ~> BS), f ∘ idS == f.
Proof.
  intros. simpl. arrequiv.
Qed.

                                           
Lemma preview_comp :
  forall {A} {B} {C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C}
         (l : forall {f fS} {func : @Functor f fS}, (BS ~~> fS _ BS) ~> (AS ~~> fS _ AS))
         (l2 : forall {f fS} {func : @Functor f fS}, (CS ~~> fS _ CS) ~> (BS ~~> fS _ BS)),
    preview (l ∘ l2) == preview l >=> preview l2.
Proof.
  intros. simpl_equiv. unfold compM, _compM. normalize.  unfold preview.  repeat rewrite comp_eval. simpl bind.  unfold maybe_bind. normalize. unfold ConstMaybeIsoS', ConstIsoS'. normalize. unfold ConstIso'. normalize_monad. unfold preview. normalizecomp. unfold ConstMaybeIsoS'. unfold ConstIsoS', ConstIso'. normalize. rewrite (flip_lens l). rewrite (flip_lens l). unfold comp at 3. unfold eval. repeat rewrite projF_injF. setoid_rewrite eval_injF. normalize. 
 *)

(* Definition ASetter' A B {AS : Setoid A} {BS : Setoid B} :=
  (BS ~~> IdentityS BS) ~> (AS ~~> IdentityS AS).

Definition Getting A B {AS : Setoid A} {BS : Setoid B} :=
  (BS ~~> ConstS BS BS) ~> (AS ~~> ConstS BS AS). *)
