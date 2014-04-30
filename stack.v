(** * The Stack Datatype
 
The Stack is the first data type defined in chapter 2 of PFDS.

Its signature is defined as (in SML):

<<
signature STACK = 
sig
  type a Stack
  
  val empty       :: a Stack
  val isEmpty     :: a Stack -> bool

  val cons        :: a x a Stack -> a Stack
  val head        :: a Stack -> a
  val tail        :: a Stack -> a Stack
end
>>
*)

(** ----- *)

Require Import Bool Arith.

(** ** The Implementation *)

(** A stack is either empty, or it is constructed from a series of Cons.

    That is, the list that would be expressed in Haskell as <<[1, 2, 3]>> would
    be represented herein as [Cons nat 1 (Cons nat 2 (Cons nat 3 (Empty nat)))].
 *)

Inductive stack (T:Type) : Type :=
  | Empty : stack T
  | Cons : T -> stack T -> stack T.


(** An empty stack is represented by the value Empty; therefore, an
    implementation of isEmpty only needs to match that value.
 *)

Definition isEmpty T (s : stack T) : bool :=
  match s with
    | Empty => true
    | _     => false
  end.

(** Retrieving the head of the list poses some interesting problems. The book
    desires an exception be raised for the head of an empty list; however, a
    formally verified program shouldn't have any erroneous conditions. There
    is very likely a better way to express this in a definition, but this is
    day 3 with the language. For now, an option property will suffice. This
    returns None for an empty list, and Some value for the non-empty stack.
 *)

Definition head T (s : stack T) : option T :=
  match s with
    | Empty => None
    | Cons s' _ => Some s'
  end.

Definition tail T (s : stack T) : stack T :=
  match s with
    | Empty => Empty T
    | Cons _ s' => s'
  end.

(** In order to allow cons to take a head, the value has to have the option
    property.
  *)

Definition cons T (x : option T) (s : stack T) : stack T :=
  match x with
    | None => s
    | Some x' => Cons T x' s
  end.

Fixpoint length T (s : stack T) : nat :=
  match s with
    | Empty => 0
    | Cons _ s' => 1 + (length T s')
  end.


(** ----- *)
(** ** Some examples *)

(** *** The empty stack. *)

Eval simpl in Empty nat. (** <<= Empty nat : stack nat >>*)
Eval simpl in isEmpty nat (Empty nat). (** <<= true : bool >> *)

(** *** A stack of length 1. *)

Eval simpl in Cons nat 1 (Empty nat). (** <<= Cons nat 1 (Empty nat) : stack nat >> *)
Eval simpl in isEmpty nat (Cons nat 1 (Empty nat)). (** <<= false : bool >>*)

(** *** Heads or tails? *)
Definition list1 := Cons nat 1 (Empty nat).
Definition list2 := Cons nat 2 list1.
Definition list3 := Cons nat 2 (Cons nat 1 (Empty nat)).

Eval simpl in head nat list1. (** <<= Some 1 : option nat>> *)
Eval simpl in head nat list2. (** <<= Some 2 : option nat>> *)
Eval simpl in tail nat list1. (** <<= Empty nat : stack nat>> *)
Eval simpl in tail nat list2. (** <<= list1 : stack nat>> *)
Eval simpl in head nat (tail nat list2). (** <<= Some 1 : option nat>> *)
Eval simpl in length nat list2. (** <<= 2 : nat>> *)
Eval simpl in cons nat (head nat list3) (tail nat list3).

Eval simpl in cons nat (head nat list2) (tail nat list2).

(** ----- *)
(** ** Proving head/tail consistency.

   Theorem: consing the head of a list onto the tail of a list returns the
   original list. *)

Theorem head_tail_consistency: forall t s,
  cons t (head t s) (tail t s) = s. 
Proof.
  (** Prologue: _dramatis personae_ and split the proof into two cases: one in
     which the stack is empty, and the other when the stack is not empty. *)

  intros. induction s.

  (** Case 1: the stack is empty. *)

  reflexivity.

  (** Case 2: the stack is not empty. *)

  rewrite <- IHs.
  reflexivity.
Qed.


(** ** The extracted program (in OCaml) *)

(*
Extraction "stack.ml" stack isEmpty head tail cons length list1 list2.
Extraction Language Haskell.
Extraction "stack.hs" stack isEmpty head tail cons length list1 list2.
 *)

(**
<<
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

(** val plus : nat -> nat -> nat **)

let rec plus n m =
  match n with
  | O -> m
  | S p -> S (plus p m)

type 't stack =
| Empty
| Cons of 't * 't stack

(** val isEmpty : 'a1 stack -> bool **)

let isEmpty = function
| Empty -> True
| Cons (t, s0) -> False

(** val head : 'a1 stack -> 'a1 option **)

let head = function
| Empty -> None
| Cons (s', s0) -> Some s'

(** val tail : 'a1 stack -> 'a1 stack **)

let tail = function
| Empty -> Empty
| Cons (t, s') -> s'

(** val cons : 'a1 option -> 'a1 stack -> 'a1 stack **)

let cons x s =
  match x with
  | Some x' -> Cons (x', s)
  | None -> s

(** val length : 'a1 stack -> nat **)

let rec length = function
| Empty -> O
| Cons (t, s') -> plus (S O) (length s')
>>
*)

Eval simpl in tail nat (Empty nat).
Eval simpl in head nat (Cons nat 1 (Empty nat)).