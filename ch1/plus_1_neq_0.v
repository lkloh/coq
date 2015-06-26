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

                       

Theorem plus_1_neq_O : forall n : nat,
beq_nat (n + 1) O = false.
Proof.
  intros n.
  destruct n as [| n'].
  reflexivity.
  reflexivity.
Qed.
