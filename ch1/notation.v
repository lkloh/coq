Fixpoint plus (n m : nat) : nat :=
match n with
  | O => m
  | S n' => S (plus n' m)
end. 

Notation "x + y" := (plus x y)
(at level 50, left associativity)
: nat_scope.

Fixpoint minus (n m : nat) : nat :=
  match n,m with
    | O,_ => O
    | S _, O => n
    | S n', S m' => minus n' m'
  end.

Notation "x - y" := (minus x y)
  (at level 50, left associativity)
  : nat_scope.

Fixpoint mult(n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end. 

Notation "a x b" := (mult a b)
  (at level 40, left associativity)
  : nat_scope

  







