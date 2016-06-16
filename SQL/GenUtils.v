Require Import Algebra.SetoidCat Algebra.SetoidCat.MaybeUtils Tactics Utils SetoidUtils Algebra.SetoidCat.NatUtils.
Require Import Coq.Structures.DecidableTypeEx List SetoidClass PeanoNat FMapWeakList Basics Coq.Arith.Compare_dec.

Definition ltMaybe a b :=
  caseMaybeS
    @ (ltS @ a) 
    @ False
    @ b.

Instance ltMaybe_Proper : Proper (equiv ==> equiv ==> equiv) ltMaybe.
Proof.
  solve_properS ltMaybe.
Qed.

Definition ltMaybeS := injF2 ltMaybe _.
  
