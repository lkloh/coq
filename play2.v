Module Playground2.

  Fixpoint plus (n:nat) (m:nat) : nat :=
    match n with
      | O => m
      | S n' => S (plus n' m)
    end.



