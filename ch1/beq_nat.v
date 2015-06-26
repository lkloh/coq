Fixpoint beq_nat (n m : nat) : bool :=
match n with
  | O => match m with
           | O => true
           | S m' => false
         end
  | S n' => match m with
              | O => false
              | S m' => beq_nat n' m'
            end
end.

Example test_beq_nat: beq_nat 4 5 = false.
Proof. reflexivity. Qed.

(* n <= m *)
Fixpoint ble_nat (n m : nat) : bool :=
  match n with
    | O => true
    | S n' =>
      match m with
        | O => false
        | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.

Example test_ble_nat2: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.








