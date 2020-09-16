From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

(* PLAN

 simple commands with parameter expansion
    &&, ||, !, ;
    single syscall: execve
    stretch: add & and wait
  what's it look like to verify "up to syscalls on state", i.e., if it's the same sequence, it's the same result

*)

(* ========================================================================== *)
(** ** Syntax *)

(** Variable names *)
Definition var : Set := string.

(** Characters that can be individually subject to expansion. *)
Variant char : Set :=
| CStr (s : string)
| CVar (v : var).

(** A single word, subject to expansion. *)
Definition word : Set := list char.

(** Zero or more words, subject to expansion. *)
Definition words : Set := list word.

(** Statements.

    For now, we simplify things: simple commands don't have
    assignments.  *)
Inductive stmt : Type :=
| Assign (x : var) (w : word)
| Simple (ws : words)
| Seq (s1 s2 : stmt)
| And (s1 s2 : stmt)
| Or  (s1 s2 : stmt)
| Not (s1 : stmt).

(** Exit status. *)
Definition status : Set := nat.

Definition status_ok (n : status) : bool :=
  match n with
  | O => true
  | _ => false
  end.

(** Final result of expansion. *)
Definition fields : Set := list string.

(* ========================================================================== *)
(** ** Examples *)

Section Examples.
  Variable x : var.
  Variable y : var.

  Definition x_gets_y : stmt := Assign x (cons (CVar y) nil).

  Definition x_gets_abcy : stmt := Assign x (cons (CStr "abc") (cons (CVar y) nil)).

  Definition echo_hello_x : stmt :=
    Simple (cons (cons (CStr "echo") nil) (cons (cons (CStr "hello") nil) (cons (cons (CVar x) nil) nil))).
  
End Examples.
  
(* ========================================================================== *)
(** ** Semantics *)

Variant ShellState : Type -> Type :=
| GetVar (x : var) : ShellState string
| SetVar (x : var) (s : string) : ShellState unit
| Execve (cmd : string) (args : list string) : ShellState status.

Section Denote.

  Context {eff : Type -> Type}.
  Context {HasShellState : ShellState -< eff}.

  Definition expand_char (c : char) : itree eff string :=
    match c with
    | CStr s => ret s
    | CVar x => trigger (GetVar x)
    end.

  (* TODO 2020-09-15 possibility of multiple fields (from, e.g., globbing) *)
  Fixpoint expand_word (w : word) : itree eff string :=
    match w with
    | nil => ret ""
    | cons c w' =>
      s_c <- expand_char c ;;
      s_w <- expand_word w' ;;
      ret (s_c ++ s_w)
    end.

  Fixpoint expand_words (ws : words) : itree eff fields :=
    match ws with
    | nil => ret nil
    | cons w ws' =>
      s_w <- expand_word w ;;
      f_w <- expand_words ws';;
      ret (cons s_w f_w)
    end.

  Fixpoint eval (s : stmt) : itree eff status :=
    match s with
    | Assign x w =>
      s_w <- expand_word w ;;
      trigger (SetVar x s_w) ;;
      ret 0 (* TODO 2020-09-15 failures from expansion *)  
    | Simple ws =>      
      fs <- expand_words ws ;;
      (match fs with
       | nil => ret 0
       | cons cmd args => trigger (Execve cmd args)
       end)
    | Seq s1 s2 =>
      _ <- eval s1 ;;
      eval s2
    | And s1 s2 =>
      status <- eval s1 ;;
      if status_ok status
      then eval s2
      else ret status
    | Or s1 s2 =>
      status <- eval s1 ;;
      if status_ok status
      then ret status
      else eval s2
    | Not s1 =>
      status <- eval s1 ;;
      if status_ok status
      then ret 1
      else ret 0
    end.
  
End Denote.
