
(** * Hoare: Hoare Logic, Part II *)

(***********************************************)
(* Homework 1 Part 2: 
   Define hoare logic rules for the ImpArr language,
   complete the verification of a few programs using your rules.
   There are 4 problems in this part.
***********************************************)
Require Export ImpArr.

  
(* ####################################################### *)
(** * Hoare Logic *)

(** Hoare Logic combines two beautiful ideas: a natural way of
    writing down _specifications_ of programs, and a _compositional
    proof technique_ for proving that programs are correct with
    respect to such specifications -- where by "compositional" we mean
    that the structure of proofs directly mirrors the structure of the
    programs that they are about. *)

(* ####################################################### *)
(** ** Assertions *)

(** To talk about specifications of programs, the first thing we
    need is a way of making _assertions_ about properties that hold at
    particular points during a program's execution -- i.e., claims
    about the current state of the memory when program execution
    reaches that point.  Formally, an assertion is just a family of
    propositions indexed by a [state]. *)

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.

Open Scope hoare_spec_scope.


Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.


Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st || st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.


Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.
Qed.


Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (update st X a).
 
Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).


(** Now we can give the precise proof rule for assignment: 
      ------------------------------ (hoare_asgn)
      {{Q [X |-> a]}} X ::= a {{Q}}
*)

(** We can prove formally that this rule is indeed valid. *)
(* The assignment rule is modified to take care of unsafe memory accesses *)
Definition safe_aeval a n : Assertion :=
 fun (st : state) => aeval st a = Some n.

Theorem hoare_asgn : forall Q X a,
  {{fun (st:state) => exists n, safe_aeval a n st /\ Q [X |-> n] st }}
  (X ::= a)
  {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a. intros st st' HE HQ.
  destruct HQ as [n Hs].
  destruct Hs as [Hsafe HQ].
  inversion HE.  subst.
  (* safe *)
  unfold assn_sub in HQ. 
   unfold safe_aeval in Hsafe.
   assert (J: Some n = Some n0). 
     congruence. 
   inversion J; subst; assumption. 
  (* core dump *)
    unfold safe_aeval in Hsafe.
   assert (J: Some n = None). congruence. 
   inversion J.
 Qed.


(* ####################################################### *) 
(** *** Consequence *)

(** Sometimes the preconditions and postconditions we get from the
    Hoare rules won't quite be the ones we want in the particular
    situation at hand -- they may be logically equivalent but have a
    different syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker (for
    preconditions) or stronger (for postconditions) than what we need.

    For instance, while
      {{(X = 3) [X |-> 3]}} X ::= 3 {{X = 3}},
    follows directly from the assignment rule, 
      {{True}} X ::= 3 {{X = 3}}.
    does not.  This triple is valid, but it is not an instance of
    [hoare_asgn] because [True] and [(X = 3) [X |-> 3]] are not
    syntactically equal assertions.  However, they are logically
    equivalent, so if one triple is valid, then the other must
    certainly be as well.  We might capture this observation with the
    following rule:
                {{P'}} c {{Q}}
                  P <<->> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}
    Taking this line of thought a bit further, we can see that
    strengthening the precondition or weakening the postcondition of a
    valid triple always produces another valid triple. This
    observation is captured by two _Rules of Consequence_.
                {{P'}} c {{Q}}
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ->> Q 
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
*)

(** Here are the formal versions: *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c. intros Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st'). 
  assumption. apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP. 
  apply Himp.
  apply (Hhoare st st'). 
  assumption. assumption.
Qed.

(** For example, we might use the first consequence rule like this:
                {{ True }} ->>
                {{ 1 = 1 }} 
    X ::= 1
                {{ X = 1 }}
    Or, formally... 
*)


Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c. intros Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.

(* ####################################################### *)
(** *** Skip *)

(** Since [SKIP] doesn't change the state, it preserves any
    property P:
      --------------------  (hoare_skip)
      {{ P }} SKIP {{ P }}
*)

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.
Qed.

(* ####################################################### *) 
(** *** Sequencing *)

(** More interestingly, if the command [c1] takes any state where
    [P] holds to a state where [Q] holds, and if [c2] takes any
    state where [Q] holds to one where [R] holds, then doing [c1]
    followed by [c2] will take any state where [P] holds to one
    where [R] holds:
        {{ P }} c1 {{ Q }} 
        {{ Q }} c2 {{ R }}
       ---------------------  (hoare_seq)
       {{ P }} c1;;c2 {{ R }}
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2. intros H2 H1. intros st st' H12 Pre.
  inversion H12. subst.
  apply (H2 st'0 st'). assumption.
  apply (H1 st st'0). assumption.
  apply Pre.
Qed.

(** Note that, in the formal rule [hoare_seq], the premises are
    given in "backwards" order ([c2] before [c1]).  This matches the
    natural flow of information in many of the situations where we'll
    use the rule: the natural way to construct a Hoare-logic proof is
    to begin at the end of the program (with the final postcondition)
    and push postconditions backwards through commands until we reach
    the beginning. *)

(** Informally, a nice way of recording a proof using the sequencing
    rule is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:
      {{ a = n }}
    X ::= a;;
      {{ X = n }}      <---- decoration for Q
    SKIP
      {{ X = n }}
*)

(* ####################################################### *) 
(** *** Conditionals *)

(** What sort of rule do we want for reasoning about conditional
    commands?  Certainly, if the same assertion [Q] holds after
    executing either branch, then it holds after the whole
    conditional.  So we might be tempted to write:
              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      --------------------------------
      {{P}} IFB b THEN c1 ELSE c2 {{Q}}
   However, this is rather weak. For example, using this rule,
   we cannot show that:
     {{ True }} 
     IFB X == 0
     THEN Y ::= 2
     ELSE Y ::= X + 1 
     FI
     {{ X <= Y }}
   since the rule tells us nothing about the state in which the
   assignments take place in the "then" and "else" branches. *)
   
(** But we can actually say something more precise.  In the
   "then" branch, we know that the boolean expression [b] evaluates to
   [true], and in the "else" branch, we know it evaluates to [false].
   Making this information available in the premises of the rule gives
   us more information to work with when reasoning about the behavior
   of [c1] and [c2] (i.e., the reasons why they establish the
   postcondition [Q]). *)
(**
              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 
*)


(** Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)
Definition safe_beval b n : Assertion :=
 fun (st : state) => beval st b = Some n.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ safe_beval b true st}} c1 {{Q}} ->
  {{fun st => P st /\ safe_beval b false st}} c2 {{Q}} ->
  {{fun st => P st /\ exists n, safe_beval b n st}} 
    (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2. intros HTrue HFalse. intros st st' Hcommand HPre.
  destruct HPre as [HP HE].
  inversion Hcommand. subst.
  Case "b = true". apply (HTrue st st'). assumption.
  split. assumption. assumption.
  Case "b = false". apply (HFalse st st'). assumption.
  split. assumption. assumption.
  Case "beval st b = None".
  destruct HE as [n HE']. unfold safe_beval in HE'.
  assert (J : None = Some n). congruence.
  inversion J.
Qed.




(* ####################################################### *) 

(* ####################################################### *)
(** *** Loops *)

(** Finally, we need a rule for reasoning about while loops. *)

(** Suppose we have a loop
      WHILE b DO c END
    and we want to find a pre-condition [P] and a post-condition
    [Q] such that
      {{P}} WHILE b DO c END {{Q}} 
    is a valid triple. *)

(** *** *)

(** First of all, let's think about the case where [b] is false at the
    beginning -- i.e., let's assume that the loop body never executes
    at all.  In this case, the loop behaves like [SKIP], so we might
    be tempted to write: *)

(**
      {{P}} WHILE b DO c END {{P}}.
*)

(** 
    But, as we remarked above for the conditional, we know a
    little more at the end -- not just [P], but also the fact
    that [b] is false in the current state.  So we can enrich the
    postcondition a little:
*)
(** 
      {{P}} WHILE b DO c END {{P /\ ~b}}
*)

(** 
    What about the case where the loop body _does_ get executed?
    In order to ensure that [P] holds when the loop finally
    exits, we certainly need to make sure that the command [c]
    guarantees that [P] holds whenever [c] is finished.
    Moreover, since [P] holds at the beginning of the first
    execution of [c], and since each execution of [c]
    re-establishes [P] when it finishes, we can always assume
    that [P] holds at the beginning of [c].  This leads us to the
    following rule:
*)
(** 
                   {{P}} c {{P}}
        -----------------------------------  
        {{P}} WHILE b DO c END {{P /\ ~b}}
*)
(** 
    This is almost the rule we want, but again it can be improved a
    little: at the beginning of the loop body, we know not only that
    [P] holds, but also that the guard [b] is true in the current
    state.  This gives us a little more information to use in
    reasoning about [c] (showing that it establishes the invariant by
    the time it finishes).  This gives us the final version of the rule:
*)
(**
               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}
    The proposition [P] is called an _invariant_ of the loop.
 *)


Lemma safe_bexp_eval_false : forall b st,
  beval st b = Some false -> (safe_beval b false) st.
Proof.
  intros. unfold safe_beval. assumption.
Qed.

Lemma safe_bexp_eval_true: forall b st,
  beval st b = Some true -> (safe_beval b true) st.
Proof.
  intros. unfold safe_beval. assumption.
Qed.

(**********************************************

  Homework 2.1: complete the following proof. 
 
 ***********************************************)
Lemma hoare_while : forall P b c,
  (P ->> (fun st => exists n, safe_beval b n st)) -> 
  {{fun st => P st /\ safe_beval b true st}} c {{P}} ->
  {{fun st => P st }}
  WHILE b DO c END 
  {{fun st => P st /\ safe_beval b false st}}.
Proof. 
  intros P b c. intros Hs Hpre. intros st st' HCommand HPre.
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  ceval_cases (induction HCommand) Case;
    try (inversion Heqwcom); subst; clear Heqwcom.
  Case "E_WhileEnd".
  split. assumption. apply safe_bexp_eval_false. assumption.
  Case "E_WhileLoop".
  apply IHHCommand2. reflexivity.
  apply (Hpre st st'). assumption.
  split. assumption. apply safe_bexp_eval_true. assumption.
  Case "E_While_fail".
  split.
  apply Hs in HPre; destruct HPre as [n HPre'];
  unfold safe_beval in HPre';
  assert (J : Some n = None); congruence; inversion J.
  apply Hs in HPre. destruct HPre as [n HPre'].
  unfold safe_beval in HPre'.
  assert (J : Some n = None). congruence. inversion J.
Qed.
 
  

Definition undef_aeval a : Assertion :=
 fun (st : state) => aeval st a = None.

Definition unalloc_aeval a : Assertion :=
 undef_aeval (ALen a).

(**********************************************

  Homework 2.2: Define the hoare triple for alloc
  and prove it correct
 
 ***********************************************)

Definition update_none (st : state) (x : id) : state :=
 match st with
   | Safe st' => Safe (fun x' => if eq_id_dec x x' then None else st' x')
   | CoreDump => CoreDump
 end.

Theorem hoare_new: forall arr a Q, 
    {{fun (st:state) =>
        exists n, safe_aeval a n st /\ Q (update st (Idx arr 0) n)
        /\ aeval st (ALen arr) = None}}
 ALLOC arr [[a]]
 {{Q}}.
Proof.
  intros arr a Q. intros st st' Hc HPre.
  destruct HPre as [n HPre'].
  destruct HPre' as [HP1 HP23].
  destruct HP23 as [HP2 HP3].
  inversion Hc. subst.
  unfold safe_aeval in HP1.
  assert (H : Some n = Some n0). congruence.
  inversion H. rewrite <- H2. assumption.
  Case "coredump".
  destruct H3 as [H3A | H3B]. subst.
  unfold safe_aeval in HP1.
  assert (J : Some n = None). congruence. inversion J.
  destruct H3B as [i H3B']. subst.
  assert (J : Some i = None). congruence. inversion J.
Qed.



Theorem hoare_new_abort: forall arr a Q, 
    {{fun (st:state) =>
        exists n, safe_aeval a n st /\ aeval st (ALen arr) = None }}
 ALLOC arr [[a]]
 {{Q}}.
Proof.
  intros arr a Q. intros st st' Hc HPre.
  destruct HPre as [n HPre'].
  destruct HPre' as [HP1 HP2].
  inversion Hc. subst.
  unfold safe_aeval in HP1. admit.
  Case "coredump".
  destruct H3 as [H3A | H3B]. subst.
  unfold safe_aeval in HP1.
  assert (J : Some n = None). congruence. inversion J.
  destruct H3B as [i H3B'].
  assert (J : Some n = None). congruence. inversion J.
Qed.
  
  
  
  

(**********************************************

  Homework 2.3: Define the hoare triple for write
  and prove it correct
 
 ***********************************************)
Theorem hoare_write : forall Q  a i x,
    {{fun (st:state) =>
        exists m, safe_aeval x m st /\
        exists n, safe_aeval i n st /\
        Q [(Idx a n) |-> m] st }} 
  (WRITE a [[i]] x)
  {{Q}}.
Proof.
  intros Q a i x. intros st st' Hcommand HPre.
  destruct HPre as [m' HPre']. destruct HPre' as [H1 H23].
  destruct H23 as [n' H23']. destruct H23' as [H2 H3].
  inversion Hcommand. subst.
  Case "safe_aeval i n".
  unfold assn_sub in H3.
  unfold safe_aeval in H1. unfold safe_aeval in H2.
  assert (SameM : m' = m). congruence.
  assert (SameN : n' = n). congruence.
  rewrite <- SameM. rewrite <- SameN. apply H3.
  Case "CoreDump".
  subst. unfold assn_sub in H3.
  destruct H7 as [Hinone | Hxnone].
  unfold safe_aeval in H2.
  assert (J : Some n' = None). congruence. inversion J.
  unfold safe_aeval in H1.
  assert (J : Some m' = None). congruence. inversion J.
Qed.
  
  


Definition prog1 :=  
(ALLOC A [[ANum 10]]);;
(ALLOC A [[ANum 20]]).

Definition crash st := st = CoreDump.

(* A few execises to test your new rules *)
Lemma hoare_prog1: 
 {{fun st => st =  empty_state}} prog1 
{{crash}}.
Proof. 
 Admitted.

Definition safe st := exists st', st = Safe st'.
Definition prog2 :=  
(ALLOC A [[ANum 10]]);;
(WRITE A [[ANum 9]] ANum 9).

Lemma hoare_prog2: 
 {{fun st => st = empty_state}} prog2 
{{safe}}.
Proof. 
 Admitted. 

Definition prog3 :=  
(ALLOC A [[ANum 10]]);;
(WRITE A [[ANum 11]] ANum 9).

Lemma hoare_prog3: 
 {{fun st => st = empty_state}} prog3
{{crash}}.
Proof. 
 Admitted. 

(**********************************************

  Homework 2.4: Analyze the following program.
 This program mimics a protocol that acquires and releases locks of resources.
 The locks to resources are represented as an array. 
 The first loop initialized all locks to be unlocked (set to 0).
 The second loop acquires all locks by setting all array elements to 1. 
 The last loop releases all locks by decrementing all array elements by 1. 
 
 ***********************************************)
Definition prog4 : com := 
  Z ::= ANum 10;;
  (ALLOC A [[AId Z]]);;
  Y ::= (ANum 1);;
  WHILE (BLe (AId Y) (AId Z)) DO
    (WRITE A [[AId Y]] (ANum 0));;
   Y ::= APlus (AId Y) (ANum 1) 
  END;; 
  Y ::= (ANum 1);;
  WHILE (BLe (AId Y) (AId Z)) DO
    (WRITE A [[AId Y]] (ANum 1));;
   Y ::= APlus (AId Y) (ANum 1) 
  END;;
  Y ::= (AId Z);;
  WHILE (BLe (ANum 1) (AId Y) ) DO
    (WRITE A [[AId Y]] (AMinus (AArr A (AId Y)) (ANum 1)));;
   Y ::= AMinus (AId Y) (ANum 1) 
  END.

(* We need inductively defined properties for our analysis *)

(* all_zero st A n means that all elements of A up to n are 0 *)
Inductive all_zero: state -> id -> nat -> Prop :=
| All_zero_base: forall st a, all_zero st a 0
| All_zero_succ: forall st a n,
    aeval st (AArr a (ANum (S n)))= Some 0 -> all_zero st a n ->
    all_zero st a (S n).

Inductive all_one: state -> id -> nat -> Prop :=
| All_one_base: forall st a, all_one st a 0
| All_one_succ: forall st a n,
    aeval st (AArr a (ANum (S n)))= Some 1 -> all_one st a n ->
    all_one st a (S n).

Print empty_state.

(* Prove the following Hoare triple. 
   You may need to define your own inductive properties. *)
Lemma hoare_prog4 :
 {{fun st => st = empty_state}}
 prog4
 {{fun st =>exists n, aeval st (ALen A) = Some n /\ all_zero st A n}}.
Proof. 
  eapply hoare_seq. eapply hoare_seq. eapply hoare_seq. eapply hoare_seq.
  eapply hoare_seq. eapply hoare_seq. eapply hoare_seq.
  eapply hoare_consequence_post.
  apply hoare_while.
  Case "loop body preserves invariant".
  intros st H.
  apply H.
  unfold hoare_triple. intros.
  destruct H0 as [H1 H2].
  destruct H1 as [n H1']. exists n. 
  Abort.
  
  


  
(* ####################################################### *)
(** ** Complete List of Hoare Logic Rules *)

(** Above, we've introduced Hoare Logic as a tool to reasoning
    about Imp programs. In the reminder of this chapter we will
    explore a systematic way to use Hoare Logic to prove properties
    about programs. The rules of Hoare Logic are the following: *)

(**
             ------------------------------ (hoare_asgn)
             {{Q [X |-> a]}} X::=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} SKIP {{ P }}

               {{ P }} c1 {{ Q }} 
               {{ Q }} c2 {{ R }}
              ---------------------  (hoare_seq)
              {{ P }} c1;;c2 {{ R }}

              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
    In the next chapter, we'll see how these rules are used to prove
    that programs satisfy specifications of their behavior.
*)

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

