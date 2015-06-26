Definition andb2 (b2:bool) (b3:bool) : bool :=
match b2 with
  | true => b3
  | false => false
end.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
match b1 with
  | true => (andb2 b2 b3)
  | false => false
end.


Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.


