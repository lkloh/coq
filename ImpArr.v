(** * Based on Imp: Simple Imperative Programs *)
(** * Based on ImpArr adds to the state arrays *)

Require Export SfLib.

(* ##################################################### *)
(** ** Identifiers *)

(** To begin, we'll need to formalize _identifiers_ such as program
    variables.  We could use strings for this -- or, in a real
    compiler, fancier structures like pointers into a symbol table.
    But for simplicity let's just use natural numbers as identifiers. *)

(** (We hide this section in a module because these definitions are
    actually in [SfLib], but we want to repeat them here so that we
    can explain them.) *)

(** We define a new inductive datatype [Id] so that we won't confuse
    identifiers and numbers.  We use [sumbool] to define a computable
    equality operator on [Id]. *)

(* "Id n" represents a variable *)
(* "Idx a n" represents the nth element of array a *)
Inductive id : Type :=
 | Id : nat -> id
 | Idx : id -> nat -> id. (* <--- new for array*)


Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof. 
   intro id1.  
   induction id1; intro id2; destruct id2 as [n21 | n22].
   destruct (eq_nat_dec n n21) as [Heq | Hneq].
   Case "Id n1 = Id n2".
     left. rewrite Heq. reflexivity.
   Case "Id n1 <> Id n2".
     right. intros contra. inversion contra. apply Hneq. apply H0.
  Case "Id n1 <> Idx n2".
     right. intros contra. inversion contra. 
  Case "Idx n1 <> Id n2".
     right. intros contra. inversion contra. 

  destruct (IHid1 n22) as [Heq | Hneq]. 
     destruct (eq_nat_dec n n0) as [Heqi | Hneqi].
  Case "Idx n1 = Idx n2".
    left; subst; auto.
   Case "Idx n n1 <> Idx n n2".
     right; intro J; inversion J; subst; apply Hneqi; auto.
  Case "Idx n1 n <> Idx n2 n".
     right; intro J; inversion J; subst; apply Hneq; auto.
Qed.
(*Defined. *)


(** The following lemmas will be useful for rewriting terms involving [eq_id_dec]. *)

Lemma eq_id : forall (T:Type) x (p q:T), 
              (if eq_id_dec x x then p else q) = p. 
Proof.
  intros. 
  destruct (eq_id_dec x x). 
  Case "x = x". 
    reflexivity.
  Case "x <> x (impossible)". 
  apply ex_falso_quodlibet. apply n. reflexivity.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof.
 intros. 
 destruct (eq_id_dec x y).
 contradiction. (* assert (J:= H e).  inversion J. *)
 reflexivity.
Qed.
(** [] *)


(* End Id. *)

(* ####################################################### *)
(** ** States *)
 
(** A _state_ represents the current values of _all_ the variables at
    some point in the execution of a program. *)
(** For simplicity (to avoid dealing with partial functions), we
    let the state be defined for _all_ variables, even though any
    given program is only going to mention a finite number of them. 
    The state captures all of the information stored in memory.  For Imp
    programs, because each variable stores only a natural number, we
    can represent the state as a mapping from identifiers to [nat].  
    For more complex programming languages, the state might have more 
    structure.  
*)

(* We distinguish between a well-formed state and a crashed state.
   CoreDump results from unsafe access to the state 
   such as double allocation and out of bounds access.

   We assume the A[0] stores the length of array A. 
   Accesses to A[i] where 0< A < A[0]+1 is safe
*)

Inductive state :=
| Safe: (id -> option nat) -> state
| CoreDump: state. 

Definition empty_state : state :=
  Safe (fun _ => None ).

(* read returns (Some n) if the access is safe 
   and x is mapped to n in the state; 
   returns None otherwise
*)
Definition read (st: state) (x: id) : option nat :=
 match st with
 | Safe st' =>       
   match x with 
     | Idx a 0 => st' x
     | Idx a (S i) => 
        (match st' (Idx a 0) with
           | Some b =>  
             if (ble_nat i b) then st' x
             else None
           | None => None
         end)
     | _ => st' x
   end
 | CoreDump => None
 end.

(* update returns a new Safe state if the write is safe; 
   returns CoreDump otherwise
*)
Definition update (st : state) (x : id) (n : nat) : state :=
 match st with
   | Safe st' => 
     match x with
       | Idx a 0 =>  
          match st' (Idx a 0) with
              | Some _ => CoreDump
              | None =>
                Safe (fun x' => if eq_id_dec x x' then Some (n) else st' x')
          end
       | Idx a (S i) => 
         match st' (Idx a 0) with
              | Some m => 
                if (ble_nat (S i) m) then 
                  Safe (fun x' => if eq_id_dec x x' then Some (n) else st' x')
                else CoreDump
              | None => CoreDump
         end
       | _ => Safe (fun x' => if eq_id_dec x x' then Some (n) else st' x')
     end
 | CoreDump => CoreDump
 end.
   

Theorem update_eq1 : forall n x st,
  read (update (Safe st) (Id x) n) (Id x) = Some n.
Proof.
  intros. 
  unfold update. unfold read. apply eq_id.
Qed.
(** [] *)


Theorem update_neq1 : forall x2 x1 n st,
  Id x2 <> Id x1 ->                        
  read (update st (Id x2) n) (Id x1) = read st (Id x1).
Proof.
intros. 
  unfold update; unfold read. 
 destruct st; simpl.
 apply neq_id. apply H.
 reflexivity.
Qed.



(* ################################################### *)
(** ** Syntax  *)

(** We can add variables to the arithmetic expressions we had before by
    simply adding one more constructor: *)

(* array element A[i] is encoded as AArr A (ANum i)
   ALen A evaluates to the length of A, which is stored at A[0]
 *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp               
  | AArr : id -> aexp -> aexp  (*<-- new *)             
  | ALen : id -> aexp (*<-- nw *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" 
  | Case_aux c "AArr" | Case_aux c "ALen"  | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

(**  definition a few arrays. 
    These can be viewed as global variables **)
Definition A : id := Id 3.
Definition B : id := Id 4.
Definition C : id := Id 5.


(** The definition of [bexp]s is the same as before (using the new
    [aexp]s): *)

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].

(* ################################################### *)
(** ** Evaluation  *)

(** The arith and boolean evaluators can be extended to handle
    variables in the obvious way: *)

Fixpoint aeval (st : state) (a : aexp) : option nat :=
  match a with
  | ANum n => Some n
  | AId x => read st x                                  
  | AArr x a => match (aeval st a) with 
                | Some n => read st (Idx x n)
                | None => None
              end
     (* <----- NEW *)
  | ALen x => read st (Idx x 0)
     (* <----- NEW *)
  | APlus a1 a2 => match ( (aeval st a1), (aeval st a2)) with
                     |(Some b1, Some b2) => Some (b1 + b2)
                     | _ => None
                   end
  | AMinus a1 a2  => match ( (aeval st a1), (aeval st a2)) with
                     |(Some b1, Some b2) => Some (b1 - b2)
                     | _ => None
                     end
  | AMult a1 a2 =>  match ( (aeval st a1), (aeval st a2)) with
                     |(Some b1, Some b2) => Some (b1 * b2)
                     | _ => None
                    end
  end.

Fixpoint beval (st : state)  (b : bexp) : option bool :=
  match b with
  | BTrue       => Some true
  | BFalse      => Some false
  | BEq a1 a2   => match ( (aeval st a1), (aeval st a2)) with
                     |(Some b1, Some b2) => Some (beq_nat b1 b2)
                     | _ => None
                   end 
  | BLe a1 a2   => match ( (aeval st a1), (aeval st a2)) with
                     |(Some b1, Some b2) => Some (ble_nat b1 b2)
                     | _ => None
                   end 
  | BNot b1     => match (beval st b1) with
                     | Some b2 => Some (negb b2)
                     | _ => None
                   end 
  | BAnd b1 b2  => match ( (beval st b1), (beval st b2)) with 
                     |(Some b3, Some b4) => Some (andb b3 b4)
                     | _ => None
                   end 
  end.


(* the commands are updated to include array allocation and update 
   CWrite A i e updates the ith element of A by e.
   CAlloc A n allocates n cells for array A.
   allocation can be done only once for each array.
*)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CWrite : id -> aexp -> aexp -> com (*<-- New *)
  | CAlloc: id -> aexp -> com (*<-- New *)
.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";;"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "WRITE" | Case_aux c "ALLOC" ].

(** As usual, we can use a few [Notation] declarations to make things
    more readable.  We need to be a bit careful to avoid conflicts
    with Coq's built-in notations, so we'll keep this light -- in
    particular, we won't introduce any notations for [aexps] and
    [bexps] to avoid confusion with the numerical and boolean
    operators we've already defined.  We use the keyword [IFB] for
    conditionals instead of [IF], for similar reasons. *)

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'WRITE' a1 '[[' a2 ']]' a3"  :=
  (CWrite a1 a2 a3) (at level 100).
Notation "'ALLOC' i '[[' a ']]'"  :=
  (CAlloc i a) (at level 79 , right associativity).

(** For example, here is the factorial function again, written as a
    formal definition to Coq: *)

Definition loop : com := 
  (ALLOC X [[ANum 10]]);;
  Y ::= (ANum 0);;
  WHILE (BLe (AId Y) (ANum 10)) DO
   WRITE X[[AId Y]] (AId Y)
  END.

(* ################################################################ *)
(** * Evaluation *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [WHILE] loops don't necessarily terminate makes defining
    an evaluation function tricky... *)

(* #################################### *)
(** ** Evaluation as a Relation *)

(** Here's a better way: we define [ceval] as a _relation_ rather than
    a _function_ -- i.e., we define it in [Prop] instead of [Type], as
    we did for [aevalR] above. *)

(** This is an important change.  Besides freeing us from the awkward
    workarounds that would be needed to define evaluation as a
    function, it gives us a lot more flexibility in the definition.
    For example, if we added concurrency features to the language,
    we'd want the definition of evaluation to be non-deterministic --
    i.e., not only would it not be total, it would not even be a
    partial function! *)
(** We'll use the notation [c / st || st'] for our [ceval] relation:
    [c / st || st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']".

*)

(** Here is the formal definition.  (Make sure you understand
    how it corresponds to the inference rules.) *)

Reserved Notation "c1 '/' st '||' st'" 
 (at level 40, st at level 39).
(* the evaluation relations are augmented with new rules to handle 
   array operations and unsafe memory accesses*)

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Ass_s  : forall st a1 n x,
      aeval st a1 = Some n ->
      (x ::= a1) / st || update st x n
  | E_Ass_f  : forall st a1 x,
      aeval st a1 = None ->
      (x ::= a1) / st || CoreDump
  (*<-- NEW 
    if a1 evaluates to None, which indicates this is an unsafe access,
    the state crashes
   *)
 | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || st' ->
      c2 / st' || st'' ->
      (c1 ;; c2) / st || st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = Some true ->
      c1 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = Some false ->
      c2 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st|| st'
 | E_If_f : forall st  b c1 c2,
      beval st b = None ->
      (IFB b THEN c1 ELSE c2 FI) / st|| CoreDump
  (* <-- New *)
  | E_WhileEnd : forall b st c,
      beval st b = Some false ->
      (WHILE b DO c END) / st || st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = Some true ->
      c / st || st' ->
      (WHILE b DO c END) / st' || st'' ->
      (WHILE b DO c END) / st || st''
  | E_While_f : forall b st c,
      beval st b = None ->
      (WHILE b DO c END) / st || CoreDump
  (* <-- New *)
   | E_Alloc: forall st size n a,
       aeval st size = Some n ->
       aeval st (ALen a) = None ->
      (ALLOC a [[size]]) / st ||  update st (Idx a 0) n
   (* when allocating memory for an array, 
      we check that the size expression can be evaluated, 
      and that the array has not been allocated before. 
      The size of the array is written to the 0th element *)
  | E_Alloc_f: forall st size a ,
       aeval st size = None \/  (exists i, aeval st (ALen a) = Some i)->
      (ALLOC a [[size]]) / st ||  CoreDump
   | E_Write: forall st x n m a b,
       aeval st x = Some n ->
       aeval st b = Some m -> 
      (WRITE a [[x]] b) / st || update  st (Idx a n) m
   (* the update function returns CoreDump for all unsafe accesess*)
  | E_Write_f: forall st x a b,
      (aeval st x = None \/ 
       aeval st b = None) -> 
       (WRITE a [[x]] b) / st || CoreDump

  where "c1 '/' st '||' st'" := (ceval c1 st st').




Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass_s" | Case_aux c "E_Ass_fail" 
    | Case_aux c "E_Seq"| Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
    | Case_aux c "E_If_fail" | Case_aux c "E_WhileEnd" 
    | Case_aux c "E_WhileLoop" |Case_aux c "E_While_fail"
    | Case_aux c "E_Alloc" |Case_aux c "E_Alloc_fail"
    | Case_aux c "E_Write" |Case_aux c "E_Write_fail"
 ].

(** *** *)
(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)

Example ceval_example1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   || (update (update empty_state X 2) Z 4).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq  with (update empty_state X 2).
  Case "assignment command".
    apply E_Ass_s. reflexivity.
    Case "if command".
    apply E_IfFalse.
      simpl. rewrite (eq_id _ X). auto. 
      apply E_Ass_s. reflexivity.
Qed.

(** **** Exercise: 2 stars (ceval_example2)  *)
Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
  (* FILL IN HERE *) 
   apply E_Seq  with (update empty_state X 0).
   Case "assignment x". 
     apply E_Ass_s.  reflexivity. 
   apply E_Seq  with (update (update empty_state X 0) Y 1).
   Case "assignment y". 
     apply E_Ass_s.  reflexivity. 
   Case "assignment z". 
     apply E_Ass_s.  reflexivity. 
Qed.



(* ####################################################### *)
(** ** Determinism of Evaluation *)

(** Changing from a computational to a relational definition of
    evaluation is a good move because it allows us to escape from the
    artificial requirement (imposed by Coq's restrictions on
    [Fixpoint] definitions) that evaluation should be a total
    function.  But it also raises a question: Is the second definition
    of evaluation actually a partial function?  That is, is it
    possible that, beginning from the same state [st], we could
    evaluate some command [c] in different ways to reach two different
    output states [st'] and [st'']?

    In fact, this cannot happen: [ceval] is a partial function.
    Here's the proof: *)

(* <$Date: 2014-12-26 15:20:26 -0500 (Fri, 26 Dec 2014) $ *)

