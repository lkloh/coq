Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => b2 
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => true
  | false => b2
  end.

    

Theorem andb_eq_orb : forall (b c : bool),
  (andb b c = orb b c) -> (b = c).
Proof.
  intros b c H.
  destruct b.
  destruct c.
  reflexivity.
  rewrite <- H.
  

  




  