
(* 1. Define an inductive data type myOdd: nat -> Set,
 so that you can prove the following lemma: 
 forall n, myOdd n -> exists m, n = 2*m +1 *)


Inductive myOdd : nat -> Set :=
| m_1 : myOdd 1
| m_IH : forall n : nat, myOdd n -> myOdd (S (S n)).

Check myOdd.

Lemma plus_0_r: forall r : nat,
  r + 0 = r.
Proof.
  intros r.
  induction r as [| r'].
  reflexivity.
  simpl. rewrite -> IHr'. reflexivity.
Qed.

Lemma n_eq_m__Sn_eq_Sm : forall (n m : nat),
  n = m -> S n = S m.
Proof.
  intros n.
  destruct n as [| n'].
    intros m H. rewrite <- H. reflexivity.
    intros m H. rewrite -> H. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, 
  n + (S m) = S (n + m).
Proof.
  admit.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n'].
  simpl. rewrite -> plus_0_r. reflexivity.
  simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.


Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  induction n as [| n'].
  simpl. reflexivity.
  simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Lemma expand_S : forall n : nat,
  S n = n + 1.
Proof.
    intros n.
    induction n.
    reflexivity.
    simpl. rewrite <- IHn. reflexivity.
Qed.

Lemma plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  reflexivity.
  simpl. rewrite -> IHn'. reflexivity.
Qed.
 

Lemma myOdd_lemma : forall n,
  myOdd n -> (exists m, n = 2*m + 1).
Proof.
  intros n.
  intros H.
  induction n as [| n'].
    inversion H.
    induction H as [| ].
      exists 0. reflexivity.
      inversion IHmyOdd.
      exists (x + 1).
      rewrite -> expand_S.
      rewrite -> expand_S.
      rewrite -> H0.
      assert (HH : 2 * (x + 1) = 2 * x + 2).
        simpl.
        rewrite -> plus_0_r.
        simpl.
        destruct x.
        simpl. reflexivity.
        rewrite -> plus_0_r.
        rewrite -> plus_swap.
        rewrite <- plus_assoc.
        assert (two : 2 = 1 + 1). reflexivity.
        rewrite <- two.
        rewrite <- plus_assoc.
        reflexivity.
        rewrite <- plus_assoc.
        assert (two : 2 = 1 + 1). reflexivity.
        rewrite <- two.
        rewrite -> HH.
        rewrite <- plus_assoc.
        simpl.
        assert (three : 3 = 2 + 1). reflexivity.
        rewrite -> three.
        rewrite -> plus_assoc.
        reflexivity.
Qed.
        

(* 2. Define myOdd2 and myEven2 mutually inductively. 
   Prove the lemma: forall n, myOdd2 n -> exists m, n = 2*m +1. *)

(*
  Inductive myEven2: nat -> Set :=
    | e2_1 : myEven2 0
    | e2_IH : forall n : nat, myOdd2 n -> myEven2 (S n)
  with myOdd2 : nat -> Set :=
    | o2_IH : forall n : nat, myEven2 n -> myOdd2 (S n).
*)

Inductive myOdd2: nat -> Set :=
  | o2_1 : myOdd2 1
  | o2_IH : forall n : nat, myEven2 n -> myOdd2 (S n)
with myEven2 : nat -> Set :=
  | e2_IH : forall n : nat, myOdd2 n -> myEven2 (S n).

Check myOdd2_ind.

Example myOdd2_test_1:
  myOdd2 1.
Proof.
  apply o2_1.
Qed.


Example myOdd2_test_2:
  myOdd2 5.
Proof.
  apply o2_IH.
  apply e2_IH.
  apply o2_IH.
  apply e2_IH.
  apply o2_1.

Example myEven2_test_3:
  myEven2 4.
Proof.
  apply e2_IH.
  apply o2_IH.
  apply e2_IH.
  apply o2_1.
Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.
Qed.

Scheme myOdd2_mut := Induction for myOdd2 Sort Prop
  with myEven2_mut := Induction for myEven2 Sort Prop.

Check myOdd2_mut.

Lemma myOdd2_lemma_p : forall n,
  myOdd2 n -> (exists m, n = 2*m + 1).
Proof.
  apply (myOdd2_mut
    (fun no : myOdd2 => (exists mo : nat, no = 2*mo + 1) )
    (fun ne : myEven2 => (exists me : nat, S ne = 2*me + 1) )
  ).
  

  
      
      
      

      
      
      

    
  



