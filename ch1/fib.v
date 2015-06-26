Fixpoint plus (n m : nat) : nat :=
match n with
  | O => m
  | S n' => S (plus n' m)
end.

Fixpoint mult (n m : nat) : nat :=
match n with
  | O => O
  | S n' => plus m (mult n' m)
end. 

Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => 1
    | S n' => mult n (factorial n')
  end.

Example test_fac: (factorial 3) = 6.
Proof. reflexivity. Qed.

  Example test_fac2: (factorial 5) = (mult 10 12).
  Proof. simpl. reflexivity. Qed.
