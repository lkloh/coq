(* n <= m *)
Fixpoint ble_nat (n m : nat) : bool :=
match n with
  | O => true
  | S n'=>
    match m with
      | O => false
      | S m' => ble_nat n' m'
    end
end.

(* a-b *)
Fixpoint minus (a b: nat) : nat :=
  match a, b with
    | O, _ => O
    | S a', O => a
    | S a', S b' => minus a' b'
  end.


(* n < m *)
Definition blt_nat (n m : nat) : bool :=
  match m-n with
    | O => false
    | S a' => true
  end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
  
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
  
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

