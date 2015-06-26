Module Playground2.
  
Inductive bin : Type :=
| O : bin
| P : bin -> bin
| Q : bin -> bin.

Definition incr (b : bin) : bin :=
  match b with
    | O => Q O
    | P n' => Q n'
    | Q n' => P (P n')
  end.

Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
    | O => 0
    | Q O => 1
    | P b' => 2 * (bin_to_nat b')
    | Q b' => 2 * (bin_to_nat b') + 1
  end.

(* P 1 = 2 * 1 = 2 *)
Example test1: (bin_to_nat (Q O)) = 2.
Proof. reflexivity. Qed.



End Playground2.