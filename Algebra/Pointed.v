Class Pointed A : Type :=
  {
    point : A
  }
.


Instance nat_Pointed : Pointed nat :=
  {
    point := 0
  }.
