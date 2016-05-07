Require Import List.
Require Import Peano_dec.
(* Require Import PeanoNat. *)
Require Import FSetWeakList.

Require Import Coq.Structures.DecidableTypeEx.

Module FSetNat := FSetWeakList.Make Nat_as_DT.

Notation "∅" := FSetNat.empty.
Notation "a ∩ b" := (FSetNat.inter a b) (at level 11, left associativity).
Notation "a ∪ b" := (FSetNat.union a b) (at level 12, left associativity).
Notation "﹛ a ﹜" := (FSetNat.singleton a) (at level 10).
Notation "a ∈ b" := (FSetNat.In a b) (at level 15).
Notation "a ∈? b" := (FSetNat.mem a b) (at level 15).

  Lemma and_app : forall l l2, fold_right and True (l ++ l2) <-> (fold_right and True l /\ fold_right and True l2). 
  Proof.
  intros. induction l. simpl. tauto. simpl. tauto.
  Qed.
  
  Definition allTrue {T} (q : T -> Prop) (l : list T) : Prop := fold_right (fun q => fun p => q /\ p) True (map q l).

  (* Lemma eqb_x_x : forall x, x =? x = true.
  Proof.
    intros. induction x.
    * simpl. reflexivity.
    * simpl. apply IHx.
  Qed. *)
  
  Definition null {a} (l : list a) : bool :=
    match l with
      | List.nil => true
      | _ => false
    end
  .
  Ltac elim_true :=
    repeat match goal with
      | |- _ /\ _ => split ; [
            intros; auto
          | intros; auto
          ]
    end.
                                                           
Fixpoint sequence {a : Type} (l : list (option a)) : option (list a) :=
  match l with
    | List.nil => Some List.nil
    | Some b :: l' => match sequence l' with
                        | Some l'' => Some (b :: l'')
                        | None => None
                      end
    | None :: _ => None
  end
.
  Lemma let_intro : forall a b c  (z : a * b) (f : a -> b -> c), (let (x,y) := z in f x y) = f (fst z) (snd z).
  Proof.
    intros. 
    tauto.
  Qed.

  Ltac simpl_let := repeat rewrite let_intro; simpl.
  

  Ltac simpl_let_2 H := repeat rewrite let_intro in H; simpl in H.

  


Section ListDoubleInductionPrinciple.
    Variable
      (T : Type)
      (P : list T -> list T -> Prop)
      (nilnil : P List.nil List.nil)
      (nilcons : forall a b, P List.nil b -> P List.nil (a :: b))
      (consnil : forall a b, P b List.nil -> P (a :: b) List.nil)
      (conscons : forall a b c d, P b d -> P (a :: b) (c :: d)).
    
    Fixpoint list_ind_2
             (l1 l2 : list T) : P l1 l2 :=
      match l1 in list _ return P l1 l2 with
        | List.nil =>
          (fix h (l2' : list T) : P List.nil l2' :=
                 match l2' with
                   | List.nil => nilnil
                   | a :: b => nilcons a b (h b)
                 end) l2
        | a :: b =>
          (fix h (l2' : list T) : P (a :: b) l2' :=
             match l2' in list _ return P (a :: b) l2' with
               | List.nil => consnil a b (list_ind_2 b List.nil)
               | c :: d => conscons a b c d (list_ind_2 b d)
             end) l2
      end
    .
  End ListDoubleInductionPrinciple.
  Section ListTripleInductionPrinciple.
    Variable
      (T : Type)
      (P : list T -> list T -> list T -> Prop)
      (nilnilnil : P List.nil List.nil List.nil)
      (nilnilcons : forall a b, P List.nil List.nil b -> P List.nil List.nil (a :: b))
      (nilconsnil : forall a b, P List.nil b List.nil -> P List.nil (a :: b) List.nil)
      (nilconscons : forall a b c d, P List.nil b d -> P List.nil (a :: b) (c :: d))
      (consnilnil : forall a b, P b List.nil List.nil -> P (a :: b) List.nil List.nil)
      (consnilcons : forall a b c d, P b List.nil d -> P (a::b) List.nil (c :: d))
      (consconsnil : forall a b c d, P b d List.nil -> P (a :: b) (c::d) List.nil)
      (consconscons : forall a b c d e f, P b d f -> P (a :: b) (c :: d) (e::f)).
    
    Fixpoint list_ind_3
             (l1 l2 l3 : list T) : P l1 l2 l3 :=
      match l1 in list _ return P l1 l2 l3 with
        | List.nil =>
          (fix h (l2' l3' : list T) : P List.nil l2' l3' :=
                 match l2' with
                   | List.nil =>
                     (fix h' (l3'' : list T) : P List.nil List.nil l3'' :=
                        match l3'' with
                          | List.nil => nilnilnil
                          | a :: b => nilnilcons a b (h' b)
                        end) l3'
                   | a :: b =>
                     (fix h' (l3'' : list T) : P List.nil (a :: b) l3'' :=
                        match l3'' with
                          | List.nil => nilconsnil a b (h b List.nil)
                          | c :: d => nilconscons a b c d (h b d)
                        end) l3'
                 end) l2 l3
        | a :: b =>
          (fix h (l2' l3' : list T) : P (a :: b) l2' l3' :=
             match l2' in list _ return P (a :: b) l2' l3' with
               | List.nil =>
                 (fix h' (l3'' : list T) : P (a :: b) List.nil l3'' :=
                    match l3'' with
                      | List.nil => consnilnil a b (list_ind_3 b List.nil List.nil)
                      | c :: d => consnilcons a b c d (list_ind_3 b List.nil d)
                    end) l3'
               | c :: d =>
                 (fix h' (l3'' : list T) : P (a :: b) (c :: d) l3'' :=
                    match l3'' with
                      | List.nil => consconsnil a b c d (list_ind_3 b d List.nil)
                      | e :: f => consconscons a b c d e f (list_ind_3 b d f)
                    end) l3'
             end) l2 l3
      end
    .
  End ListTripleInductionPrinciple.

 (* Definition subsetR {A} (ra : relation A) P : relation {a : A | P a} :=
  fun a a2 => ra (proj1_sig a) (proj1_sig a2).

Hint Unfold subsetR.

Instance subsetR_Equivalence A (ra : relation A) (EqRA : Equivalence ra) P : Equivalence (subsetR ra P).
Proof.
  split.
  autounfold. intros. reflexivity.
    autounfold. intros. symmetry. auto.
    autounfold. intros. transitivity (proj1_sig y). auto. auto.
Qed.

Instance proj1_sig_Proper A P (SA : Setoid A) : Proper (subsetR equiv P ==> equiv) (@proj1_sig A P).
Proof.
  unfold Proper, respectful, subsetR. auto. 
Qed.

 Instance equiv_Proper A (SA : Setoid A): Proper (equiv ==> equiv ==> iff) (@equiv A SA).
Proof.
  unfold Proper, respectful. split.
  intros. transitivity x.  symmetry. auto. transitivity x0. auto. auto. 
  intros. transitivity y.  auto. transitivity y0. auto. symmetry. auto. 
Qed.

Definition funcEquiv {A B} {SB : Setoid B} := pointwise_relation A equiv.

Hint Unfold funcEquiv.

Program Instance func_Equivalence (A B : Type) (SB : Setoid B): Equivalence (@funcEquiv A B SB).

Program Instance funcSetoid A B (SA : Setoid A) (SB : Setoid B) : Setoid (A -> B) :=
  {
    equiv := funcEquiv
  }.  
*)



  
