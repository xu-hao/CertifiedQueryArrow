Require Import Utils.
Require Import List RelationClasses Relation_Definitions Morphisms Coq.Program.Basics SetoidClass.


Ltac extract_common a :=
  assert (exists t, a = t) as _H; [
    exists a; reflexivity
         | destruct _H as [? _H]; rewrite _H in *; destruct a; rewrite <- _H in *; clear _H
  ]
.

Ltac find_innermost_match a tac :=
  (lazymatch a with
           | context[match ?b with _ => _ end] => find_innermost_match b tac
           | _ => tac a
         end)
.

Ltac aux_all_cases1 a := destruct a; compute; try tauto.
Ltac all_cases1 :=
  (lazymatch goal with
           | |- context[match ?a with _ => _ end] => find_innermost_match a aux_all_cases1
           | _ := match ?a with _ => _ end |- _ : _ => aux_all_cases1 a
           | _ => try (compute; tauto); try reflexivity; simpl
         end)
.


Ltac all_cases :=
  intros; compute; repeat all_cases1
.

Ltac not_in v v0 :=
  match goal with
    | H1 : ~ FSetNat.In v _ |- _ => 
      assert (v <> v0) as ?H0; [
          let H2 := fresh "H" in intro H2; rewrite H2 in H1; apply H1; eauto using FSetNat.union_2, FSetNat.union_3, FSetNat.singleton_2
        |
        ]
  end
.
Ltac not_in_2 v c :=
  match goal with
    | H1 : ~ FSetNat.In v _ |- _ => 
      assert (~ v ∈ c) as ?H0; [
          let H2 := fresh "H" in intro H2; apply H1; eauto using FSetNat.union_2, FSetNat.union_3, FSetNat.singleton_2, FSetNat.diff_3, FSetNat.singleton_1
        |
        ]
  end
.

Ltac prove_by_inversion := match goal with
                             | H : Some _ == None |- _ => inversion H
                             | H : None == Some _ |- _ => inversion H
                             | H : _ :: _ == nil |- _ => inversion H
                             | H : nil == _ :: _ |- _ => inversion H
                           end.

Ltac prove_by_equiv := try reflexivity; try prove_by_inversion.

Ltac rewrites :=
  repeat multimatch goal with
       | H : ?x == _ |- context [?x] => rewrite H
       | H : Some ?x == _ |- context [?x] => rewrite H
                     (*     | H : liftR equiv ?x _ |- context [?x] => rewrite H*)
                        end.
Ltac rewritesr := rewrites; reflexivity. 

Ltac equiv a b := assert (a == b); [ rewrites; reflexivity | destruct a, b ; [prove_by_equiv | prove_by_equiv | prove_by_equiv | prove_by_equiv ] ].

Ltac matchequiv := match goal with
                        | |- _ (match ?a with _ => _ end) ( match ?b with _ => _ end) => equiv a b
                      end.

