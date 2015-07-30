Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Module Dictionary.

Inductive dictionary : Type :=
  | empty : dictionary 
  | record : nat -> nat -> dictionary -> dictionary.

Definition insert (key value : nat) (d : dictionary) : dictionary :=
  (record key value d).

Fixpoint find (key : nat) (d : dictionary) : natoption := 
  match d with 
  | empty => None
  | record k v d' => if (beq_natty key k) 
                       then (Some v) 
                       else (find key d')
  end.
