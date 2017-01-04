Require Import Coq.Lists.List.
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
                                                           
(*Fixpoint sequence {a : Type} (l : list (option a)) : option (list a) :=
  match l with
    | List.nil => Some List.nil
    | Some b :: l' => match sequence l' with
                        | Some l'' => Some (b :: l'')
                        | None => None
                      end
    | None :: _ => None
  end
.*)
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
Section ListDoubleInductionPrinciple'.
    Variable
      (T T' : Type)
      (P : list T -> list T' -> Prop)
      (nilnil : P List.nil List.nil)
      (nilcons : forall a b, P List.nil b -> P List.nil (a :: b))
      (consnil : forall a b, P b List.nil -> P (a :: b) List.nil)
      (conscons : forall a b c d, P b d -> P (a :: b) (c :: d)).
    
    Fixpoint list_ind_2'
             (l1 : list T)(l2 : list T') : P l1 l2 :=
      match l1 in list _ return P l1 l2 with
        | List.nil =>
          (fix h (l2' : list T') : P List.nil l2' :=
                 match l2' with
                   | List.nil => nilnil
                   | a :: b => nilcons a b (h b)
                 end) l2
        | a :: b =>
          (fix h (l2' : list T') : P (a :: b) l2' :=
             match l2' in list _ return P (a :: b) l2' with
               | List.nil => consnil a b (list_ind_2' b List.nil)
               | c :: d => conscons a b c d (list_ind_2' b d)
             end) l2
      end
    .
End ListDoubleInductionPrinciple'.
Section ListDoubleRecursionPrinciple.
    Variable
      (T T' : Type)
      (P : list T -> list T' -> Type)
      (nilnil : P List.nil List.nil)
      (nilcons : forall a b, P List.nil b -> P List.nil (a :: b))
      (consnil : forall a b, P b List.nil -> P (a :: b) List.nil)
      (conscons : forall a b c d, P b d -> P (a :: b) (c :: d)).
    
    Fixpoint list_rect_2
             (l1 : list T)(l2 : list T') : P l1 l2 :=
      match l1 in list _ return P l1 l2 with
        | List.nil =>
          (fix h (l2' : list T') : P List.nil l2' :=
                 match l2' with
                   | List.nil => nilnil
                   | a :: b => nilcons a b (h b)
                 end) l2
        | a :: b =>
          (fix h (l2' : list T') : P (a :: b) l2' :=
             match l2' in list _ return P (a :: b) l2' with
               | List.nil => consnil a b (list_rect_2 b List.nil)
               | c :: d => conscons a b c d (list_rect_2 b d)
             end) l2
      end
    .
End ListDoubleRecursionPrinciple.
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
Section ListTripleInductionPrinciple'.
    Variable
      (S T U: Type)
      (P : list S -> list T -> list U -> Prop)
      (nilnilnil : P List.nil List.nil List.nil)
      (nilnilcons : forall a b, P List.nil List.nil b -> P List.nil List.nil (a :: b))
      (nilconsnil : forall a b, P List.nil b List.nil -> P List.nil (a :: b) List.nil)
      (nilconscons : forall a b c d, P List.nil b d -> P List.nil (a :: b) (c :: d))
      (consnilnil : forall a b, P b List.nil List.nil -> P (a :: b) List.nil List.nil)
      (consnilcons : forall a b c d, P b List.nil d -> P (a::b) List.nil (c :: d))
      (consconsnil : forall a b c d, P b d List.nil -> P (a :: b) (c::d) List.nil)
      (consconscons : forall a b c d e f, P b d f -> P (a :: b) (c :: d) (e::f)).
    
    Fixpoint list_ind_3'
             (l1 : list S )(l2  : list T) (l3 :list U) : P l1 l2 l3 :=
      match l1 in list _ return P l1 l2 l3 with
        | List.nil =>
          (fix h (l2'  : list T)(l3' :list U) : P List.nil l2' l3' :=
                 match l2' with
                   | List.nil =>
                     (fix h' (l3'' : list U) : P List.nil List.nil l3'' :=
                        match l3'' with
                          | List.nil => nilnilnil
                          | a :: b => nilnilcons a b (h' b)
                        end) l3'
                   | a :: b =>
                     (fix h' (l3'' : list U) : P List.nil (a :: b) l3'' :=
                        match l3'' with
                          | List.nil => nilconsnil a b (h b List.nil)
                          | c :: d => nilconscons a b c d (h b d)
                        end) l3'
                 end) l2 l3
        | a :: b =>
          (fix h (l2' : list T)(l3' : list U) : P (a :: b) l2' l3' :=
             match l2' in list _ return P (a :: b) l2' l3' with
               | List.nil =>
                 (fix h' (l3'' : list U) : P (a :: b) List.nil l3'' :=
                    match l3'' with
                      | List.nil => consnilnil a b (list_ind_3' b List.nil List.nil)
                      | c :: d => consnilcons a b c d (list_ind_3' b List.nil d)
                    end) l3'
               | c :: d =>
                 (fix h' (l3'' : list U) : P (a :: b) (c :: d) l3'' :=
                    match l3'' with
                      | List.nil => consconsnil a b c d (list_ind_3' b d List.nil)
                      | e :: f => consconscons a b c d e f (list_ind_3' b d f)
                    end) l3'
             end) l2 l3
      end
    .
  End ListTripleInductionPrinciple'.
Section ListQuadrupleInductionPrinciple.
    Variable
      (T : Type)
      (P : list T -> list T -> list T -> list T -> Prop)
      (nilnilnilnil : P List.nil List.nil List.nil nil)
      (nilnilnilcons : forall a b, P List.nil List.nil nil b -> P List.nil List.nil nil (a :: b))
      (nilnilconsnil : forall a b, P List.nil nil b List.nil -> P List.nil nil (a :: b) List.nil)
      (nilnilconscons : forall a b c d, P nil List.nil b d -> P nil List.nil (a :: b) (c :: d))
      (nilconsnilnil : forall a b, P nil b List.nil List.nil -> P nil (a :: b) List.nil List.nil)
      (nilconsnilcons : forall a b c d, P nil b List.nil d -> P nil (a::b) List.nil (c :: d))
      (nilconsconsnil : forall a b c d, P nil b d List.nil -> P nil (a :: b) (c::d) List.nil)
      (nilconsconscons : forall a b c d e f, P nil b d f -> P nil (a :: b) (c :: d) (e::f))
      (consnilnilnil : forall y z, P z nil nil nil -> P (y :: z) List.nil List.nil List.nil)
      (consnilnilcons : forall y z a b, P z List.nil List.nil b -> P (y :: z) List.nil List.nil (a :: b))
      (consnilconsnil : forall y z a b, P z List.nil b List.nil -> P (y :: z) List.nil (a :: b) List.nil)
      (consnilconscons : forall y z a b c d, P z List.nil b d -> P (y :: z) List.nil (a :: b) (c :: d))
      (consconsnilnil : forall y z a b, P z b List.nil List.nil -> P (y :: z) (a :: b) List.nil List.nil)
      (consconsnilcons : forall y z a b c d, P z b List.nil d -> P (y :: z) (a::b) List.nil (c :: d))
      (consconsconsnil : forall y z a b c d, P z b d List.nil -> P (y :: z) (a :: b) (c::d) List.nil)
      (consconsconscons : forall y z a b c d e f, P z b d f -> P (y :: z) (a :: b) (c :: d) (e::f)).
    
    Fixpoint list_ind_4
             (l1 l2 l3 l4 : list T) : P l1 l2 l3 l4 :=
      match l1 in list _ return P l1 l2 l3 l4 with
        | List.nil =>
          (fix h (l2' l3' l4' : list T) : P List.nil l2' l3' l4' :=
                 match l2' with
                   | List.nil =>
                     (fix h' (l3'' l4'' : list T) : P List.nil List.nil l3'' l4'' :=
                        match l3'' with
                          | List.nil =>
                            (fix h'' (l4''' : list T) : P List.nil List.nil nil l4''' :=
                               match l4''' with
                                 | List.nil => nilnilnilnil
                                 | a :: b => nilnilnilcons a b (h'' b)
                               end) l4''
                          | a :: b =>
                            (fix h'' (l4''' : list T) : P List.nil List.nil (a::b) l4''' :=
                               match l4''' with
                                 | List.nil => nilnilconsnil a b (h' b nil)
                                 | c :: d => nilnilconscons a b c d (h' b d)
                               end) l4''
                        end) l3' l4'
                   | a :: b =>
                     (fix h' (l3'' l4'' : list T) : P List.nil (a :: b) l3'' l4'' :=
                        match l3'' with
                          | List.nil =>
                            (fix h'' (l4''' : list T) : P List.nil (a :: b) nil l4''' :=
                               match l4''' with
                                 | List.nil => nilconsnilnil a b (h b nil nil)
                                 | c :: d => nilconsnilcons a b c d (h b nil d)
                               end) l4''
                          | c :: d =>
                            (fix h'' (l4''' : list T) : P List.nil (a :: b) (c :: d) l4''' :=
                               match l4''' with
                                 | List.nil => nilconsconsnil a b c d (h b d nil)
                                 | e :: f => nilconsconscons a b c d e f (h b d f)
                               end) l4''
                        end) l3' l4'
                 end) l2 l3 l4
        | a :: b =>
          (fix h (l2' l3' l4' : list T) : P (a :: b) l2' l3' l4' :=
             match l2' in list _ return P (a :: b) l2' l3' l4' with
               | List.nil =>
                 (fix h' (l3'' l4'' : list T) : P (a :: b) List.nil l3'' l4'' :=
                    match l3'' with
                      | List.nil =>
                        (fix h'' (l4''' : list T) : P (a:: b) nil nil l4''' :=
                           match l4''' with
                             | List.nil => consnilnilnil a b (list_ind_4 b List.nil nil nil)
                             | c :: d => consnilnilcons a b c d (list_ind_4 b nil nil d)
                           end) l4''
                      | c :: d =>
                        (fix h'' (l4''' : list T) : P (a:: b) nil (c::d) l4''' :=
                           match l4''' with
                             | List.nil => consnilconsnil a b c d (list_ind_4 b nil d nil)
                             | e :: f => consnilconscons a b c d e f (list_ind_4 b nil d f)
                           end) l4''
                    end) l3' l4'
               | c :: d =>
                 (fix h' (l3'' l4'' : list T) : P (a :: b) (c :: d) l3'' l4'' :=
                    match l3'' with
                      | List.nil =>
                        (fix h'' (l4''' : list T) : P (a:: b) (c::d) nil l4''' :=
                           match l4''' with
                             | List.nil => consconsnilnil a b c d (list_ind_4 b d List.nil nil)
                             | e :: f => consconsnilcons a b c d e f (list_ind_4 b d List.nil f)
                           end) l4''
                      | e :: f =>
                        (fix h'' (l4''' : list T) : P (a:: b) (c::d) (e::f) l4''' :=
                           match l4''' with
                             | List.nil => consconsconsnil a b c d e f (list_ind_4 b d f nil)
                             | y :: z => consconsconscons a b c d e f y z (list_ind_4 b d f z)
                           end) l4''
                    end) l3' l4'
             end) l2 l3 l4
      end
    .
  End ListQuadrupleInductionPrinciple.
Section ListQuadrupleInductionPrinciple'.
    Variable
      (T T2 T3 T4 : Type)
      (P : list T -> list T2 -> list T3 -> list T4 -> Prop)
      (nilnilnilnil : P List.nil List.nil List.nil nil)
      (nilnilnilcons : forall a b, P List.nil List.nil nil b -> P List.nil List.nil nil (a :: b))
      (nilnilconsnil : forall a b, P List.nil nil b List.nil -> P List.nil nil (a :: b) List.nil)
      (nilnilconscons : forall a b c d, P nil List.nil b d -> P nil List.nil (a :: b) (c :: d))
      (nilconsnilnil : forall a b, P nil b List.nil List.nil -> P nil (a :: b) List.nil List.nil)
      (nilconsnilcons : forall a b c d, P nil b List.nil d -> P nil (a::b) List.nil (c :: d))
      (nilconsconsnil : forall a b c d, P nil b d List.nil -> P nil (a :: b) (c::d) List.nil)
      (nilconsconscons : forall a b c d e f, P nil b d f -> P nil (a :: b) (c :: d) (e::f))
      (consnilnilnil : forall y z, P z nil nil nil -> P (y :: z) List.nil List.nil List.nil)
      (consnilnilcons : forall y z a b, P z List.nil List.nil b -> P (y :: z) List.nil List.nil (a :: b))
      (consnilconsnil : forall y z a b, P z List.nil b List.nil -> P (y :: z) List.nil (a :: b) List.nil)
      (consnilconscons : forall y z a b c d, P z List.nil b d -> P (y :: z) List.nil (a :: b) (c :: d))
      (consconsnilnil : forall y z a b, P z b List.nil List.nil -> P (y :: z) (a :: b) List.nil List.nil)
      (consconsnilcons : forall y z a b c d, P z b List.nil d -> P (y :: z) (a::b) List.nil (c :: d))
      (consconsconsnil : forall y z a b c d, P z b d List.nil -> P (y :: z) (a :: b) (c::d) List.nil)
      (consconsconscons : forall y z a b c d e f, P z b d f -> P (y :: z) (a :: b) (c :: d) (e::f)).
    
    Fixpoint list_ind_4'
             (l1 : list T)( l2:list T2)( l3:list T3)( l4 : list T4) : P l1 l2 l3 l4 :=
      match l1 in list _ return P l1 l2 l3 l4 with
        | List.nil =>
          (fix h (l2' : list T2) (l3' : list T3) ( l4' : list T4) : P List.nil l2' l3' l4' :=
                 match l2' with
                   | List.nil =>
                     (fix h' (l3'' : list T3) (l4'' : list T4) : P List.nil List.nil l3'' l4'' :=
                        match l3'' with
                          | List.nil =>
                            (fix h'' (l4''' : list T4) : P List.nil List.nil nil l4''' :=
                               match l4''' with
                                 | List.nil => nilnilnilnil
                                 | a :: b => nilnilnilcons a b (h'' b)
                               end) l4''
                          | a :: b =>
                            (fix h'' (l4''' : list T4) : P List.nil List.nil (a::b) l4''' :=
                               match l4''' with
                                 | List.nil => nilnilconsnil a b (h' b nil)
                                 | c :: d => nilnilconscons a b c d (h' b d)
                               end) l4''
                        end) l3' l4'
                   | a :: b =>
                     (fix h' (l3'' : list T3) (l4'' : list T4) : P List.nil (a :: b) l3'' l4'' :=
                        match l3'' with
                          | List.nil =>
                            (fix h'' (l4''' : list T4) : P List.nil (a :: b) nil l4''' :=
                               match l4''' with
                                 | List.nil => nilconsnilnil a b (h b nil nil)
                                 | c :: d => nilconsnilcons a b c d (h b nil d)
                               end) l4''
                          | c :: d =>
                            (fix h'' (l4''' : list T4) : P List.nil (a :: b) (c :: d) l4''' :=
                               match l4''' with
                                 | List.nil => nilconsconsnil a b c d (h b d nil)
                                 | e :: f => nilconsconscons a b c d e f (h b d f)
                               end) l4''
                        end) l3' l4'
                 end) l2 l3 l4
        | a :: b =>
          (fix h (l2' : list T2) (l3' : list T3) (l4' : list T4) : P (a :: b) l2' l3' l4' :=
             match l2' in list _ return P (a :: b) l2' l3' l4' with
               | List.nil =>
                 (fix h' (l3'' : list T3) (l4'' : list T4) : P (a :: b) List.nil l3'' l4'' :=
                    match l3'' with
                      | List.nil =>
                        (fix h'' (l4''' : list T4) : P (a:: b) nil nil l4''' :=
                           match l4''' with
                             | List.nil => consnilnilnil a b (list_ind_4' b List.nil nil nil)
                             | c :: d => consnilnilcons a b c d (list_ind_4' b nil nil d)
                           end) l4''
                      | c :: d =>
                        (fix h'' (l4''' : list T4) : P (a:: b) nil (c::d) l4''' :=
                           match l4''' with
                             | List.nil => consnilconsnil a b c d (list_ind_4' b nil d nil)
                             | e :: f => consnilconscons a b c d e f (list_ind_4' b nil d f)
                           end) l4''
                    end) l3' l4'
               | c :: d =>
                 (fix h' (l3'' : list T3) (l4'' : list T4) : P (a :: b) (c :: d) l3'' l4'' :=
                    match l3'' with
                      | List.nil =>
                        (fix h'' (l4''' : list T4) : P (a:: b) (c::d) nil l4''' :=
                           match l4''' with
                             | List.nil => consconsnilnil a b c d (list_ind_4' b d List.nil nil)
                             | e :: f => consconsnilcons a b c d e f (list_ind_4' b d List.nil f)
                           end) l4''
                      | e :: f =>
                        (fix h'' (l4''' : list T4) : P (a:: b) (c::d) (e::f) l4''' :=
                           match l4''' with
                             | List.nil => consconsconsnil a b c d e f (list_ind_4' b d f nil)
                             | y :: z => consconsconscons a b c d e f y z (list_ind_4' b d f z)
                           end) l4''
                    end) l3' l4'
             end) l2 l3 l4
      end
    .
  End ListQuadrupleInductionPrinciple'.
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



  Section NatListDoubleInductionPrinciple.
    Variable
      (T : Type)
      (P : nat ->  list T  -> Prop)
      (onil : P 0   nil)
      (ocons : forall a b, P 0 b -> P 0 (a :: b))
      (snil : forall b, P b List.nil -> P (S b) List.nil)
      (scons : forall b c d, P b d -> P (S b) (c :: d)).
    
    Fixpoint nat_list_ind_2
             (l1 : nat) ( l2 : list T) : P l1 l2 :=
      match l1 in nat return P l1 l2 with
        | 0 =>
          (fix h' (l2' : list T) : P 0 l2' :=
             match l2' with
               | List.nil => onil
               | a :: b => ocons a b (h' b)
             end) l2
        | S b =>
          (fix h' (l2' : list T) : P (S b) l2' :=
             match l2' with
               | List.nil => snil b (nat_list_ind_2 b nil)
               | c :: d => scons b c d (nat_list_ind_2 b d)
             end) l2
      end
    .
End NatListDoubleInductionPrinciple.

Section NatListQuadrupleInductionPrinciple.
    Variable
      (T : Type)
      (P : nat -> nat -> list T -> list T -> Prop)
      (oonilnil : P 0 0 List.nil nil)
      (oonilcons : forall a b, P 0 0 nil b -> P 0 0 nil (a :: b))
      (ooconsnil : forall a b, P 0 0 b List.nil -> P 0 0 (a :: b) List.nil)
      (ooconscons : forall a b c d, P 0 0 b d -> P 0 0 (a :: b) (c :: d))
      (osnilnil : forall b, P 0 b List.nil List.nil -> P 0 (S b) List.nil List.nil)
      (osnilcons : forall b c d, P 0 b List.nil d -> P 0 (S b) List.nil (c :: d))
      (osconsnil : forall b c d, P 0 b d List.nil -> P 0 (S b) (c::d) List.nil)
      (osconscons : forall b c d e f, P 0 b d f -> P 0 (S b) (c :: d) (e::f))
      (sonilnil : forall z, P z 0 nil nil -> P (S z) 0 List.nil List.nil)
      (sonilcons : forall z a b, P z 0 List.nil b -> P (S z) 0 List.nil (a :: b))
      (soconsnil : forall z a b, P z 0 b List.nil -> P (S z) 0 (a :: b) List.nil)
      (soconscons : forall z a b c d, P z 0 b d -> P (S z) 0 (a :: b) (c :: d))
      (ssnilnil : forall z b, P z b List.nil List.nil -> P (S z) (S b) List.nil List.nil)
      (ssnilcons : forall z b c d, P z b List.nil d -> P (S z) (S b) List.nil (c :: d))
      (ssconsnil : forall z b c d, P z b d List.nil -> P (S z) (S b) (c::d) List.nil)
      (ssconscons : forall z b c d e f, P z b d f -> P (S z) (S b) (c :: d) (e::f)).
    
    Fixpoint nat_list_ind_4
             (l1 l2 : nat) ( l3 l4 : list T) : P l1 l2 l3 l4 :=
      match l1 in nat return P l1 l2 l3 l4 with
        | 0 =>
          (fix h (l2' : nat) ( l3' l4' : list T) : P 0 l2' l3' l4' :=
                 match l2' with
                   | 0 =>
                     (fix h' (l3'' l4'' : list T) : P 0 0 l3'' l4'' :=
                        match l3'' with
                          | List.nil =>
                            (fix h'' (l4''' : list T) : P 0 0 nil l4''' :=
                               match l4''' with
                                 | List.nil => oonilnil
                                 | a :: b => oonilcons a b (h'' b)
                               end) l4''
                          | a :: b =>
                            (fix h'' (l4''' : list T) : P 0 0 (a::b) l4''' :=
                               match l4''' with
                                 | List.nil => ooconsnil a b (h' b nil)
                                 | c :: d => ooconscons a b c d (h' b d)
                               end) l4''
                        end) l3' l4'
                   | S b =>
                     (fix h' (l3'' l4'' : list T) : P 0 (S b) l3'' l4'' :=
                        match l3'' with
                          | List.nil =>
                            (fix h'' (l4''' : list T) : P 0 (S b) nil l4''' :=
                               match l4''' with
                                 | List.nil => osnilnil b (h b nil nil)
                                 | c :: d => osnilcons b c d (h b nil d)
                               end) l4''
                          | c :: d =>
                            (fix h'' (l4''' : list T) : P 0 (S b) (c :: d) l4''' :=
                               match l4''' with
                                 | List.nil => osconsnil b c d (h b d nil)
                                 | e :: f => osconscons b c d e f (h b d f)
                               end) l4''
                        end) l3' l4'
                 end) l2 l3 l4
        | S b =>
          (fix h (l2' : nat) ( l3' l4' : list T) : P (S b) l2' l3' l4' :=
             match l2' in nat return P (S b) l2' l3' l4' with
               | 0 =>
                 (fix h' (l3'' l4'' : list T) : P (S b) 0 l3'' l4'' :=
                    match l3'' with
                      | List.nil =>
                        (fix h'' (l4''' : list T) : P (S b) 0 nil l4''' :=
                           match l4''' with
                             | List.nil => sonilnil b (nat_list_ind_4 b 0 nil nil)
                             | c :: d => sonilcons b c d (nat_list_ind_4 b 0 nil d)
                           end) l4''
                      | c :: d =>
                        (fix h'' (l4''' : list T) : P (S b) 0 (c::d) l4''' :=
                           match l4''' with
                             | List.nil => soconsnil b c d (nat_list_ind_4 b 0 d nil)
                             | e :: f => soconscons b c d e f (nat_list_ind_4 b 0 d f)
                           end) l4''
                    end) l3' l4'
               | S d =>
                 (fix h' (l3'' l4'' : list T) : P (S b) (S d) l3'' l4'' :=
                    match l3'' with
                      | List.nil =>
                        (fix h'' (l4''' : list T) : P (S b) (S d) nil l4''' :=
                           match l4''' with
                             | List.nil => ssnilnil b d (nat_list_ind_4 b d List.nil nil)
                             | e :: f => ssnilcons b d e f (nat_list_ind_4 b d List.nil f)
                           end) l4''
                      | e :: f =>
                        (fix h'' (l4''' : list T) : P (S b) (S d) (e::f) l4''' :=
                           match l4''' with
                             | List.nil => ssconsnil b d e f (nat_list_ind_4 b d f nil)
                             | y :: z => ssconscons b d e f y z (nat_list_ind_4 b d f z)
                           end) l4''
                    end) l3' l4'
             end) l2 l3 l4
      end
    .
End NatListQuadrupleInductionPrinciple.
