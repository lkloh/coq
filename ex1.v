Inductive bool : Type :=
| true : bool
| false : bool. 

Definition nandb (b1:bool) (b2:bool) : bool :=
match b1 with
  | true => b2
  | false => true
end.



Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.
