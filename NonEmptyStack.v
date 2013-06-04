(*
 * Copyright © 2013 http://io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)
(** The [NonEmptyStack] interface provides simple non-empty abstract stacks. *)

Require Coq.Lists.List.

Module Type Signature.

(** The type of non-empty stacks containing values of type [A]. *)
Parameter t : forall (A : Type), Type.

(** A stack containing only [x]. *)
Parameter singleton : forall {A : Type} (x : A), t A.

(** The value [x] is in stack [s]. *)
Parameter is_in : forall {A : Type} (x : A) (s : t A), Prop.

(** With decidable equality on the elements of [A], the
[is_in] predicate is decidable. *)
Parameter is_in_decidable : forall
  {A : Type}
  (e : forall (x y : A), {x = y}+{~x = y})
  (x : A)
  (s : t A),
  {is_in x s}+{~is_in x s}.

(** The stack [s] has one element. *)
Parameter is_singleton : forall {A : Type} (s : t A), Prop.

(** The [is_singleton] predicate is decidable. *)
Parameter is_singleton_decidable : forall
  {A : Type}
  (s : t A),
  {is_singleton s}+{~is_singleton s}.

(** The [singleton] stack is a singleton. *)
Parameter singleton_is : forall {A : Type} (x : A),
  is_singleton (singleton x).

(** A [singleton] stack of [x] contains [x]. *)
Parameter singleton_in : forall {A : Type} (x : A),
  is_in x (singleton x).

(** With decidable equality of [A], equality of stacks is decidable. *)
Parameter eq_decidable : forall
  {A     : Type}
  (e     : forall (x y : A), {x = y}+{~x = y})
  (s0 s1 : t A),
  {s0 = s1}+{~s0 = s1}.

(** Push the value [x] to the stack [s]. *)
Parameter push : forall {A : Type} (x : A) (s : t A), t A.

(** The result of any [x] pushed to any stack [s] is not a singleton. *)
Parameter push_not_singleton : forall {A : Type} (x : A) (s : t A),
  ~is_singleton (push x s).

(** Pushing the value [x] to the stack [s] means [x] is in [s]. *)
Parameter push_in : forall {A : Type} (x : A) (s : t A),
  is_in x (push x s).

(** Pop a value from the stack [s]. *)
Parameter pop : forall {A : Type} (s : t A), A * (option (t A)).

(** Peek at the value on top of the stack [s]. *)
Parameter peek : forall {A : Type} (s : t A), A.

(** View the stack [s] as a list of elements. The first element
    of the list represents the top of the stack. *)
Parameter peek_list : forall {A : Type} (s : t A), list A.

(** All of the elements returned by [peek_list] are in [s]. *)
Parameter peek_list_in : forall {A : Type} (s : t A) (x : A),
  List.In x (peek_list s) <-> is_in x s.

(** The list returned by [peek_list] is never empty. *)
Parameter peek_list_not_empty : forall {A : Type} (s : t A),
  peek_list s <> nil.

(** Predicates that hold for all elements of [s]. *)
Parameter for_all : forall
  {A : Type}
  (P : A -> Prop)
  (s : t A), Prop.

(** If [P] holds for all in [s], and [P x], then [P] holds for all in [push x s]. *)
Parameter for_all_push : forall
  {A : Type}
  (P : A -> Prop)
  (s : t A)
  (x : A),
  for_all P s -> P x -> for_all P (push x s).

(** If [P] holds for [x], then it holds for the [singleton]. *)
Parameter for_all_singleton : forall
  {A : Type}
  (P : A -> Prop)
  (x : A),
  P x -> for_all P (singleton x).

(** If [P] holds for all in [s], and [P -> Q], then [Q] holds for all in [s]. *)
Parameter for_all_implication : forall
  {A  : Type}
  (P  : A -> Prop)
  (Q  : A -> Prop)
  (PQ : forall x, P x -> Q x)
  (s  : t A),
  for_all P s -> for_all Q s.

(** If [for_all P s], and [x] is in [s], then [P x]. *)
Parameter for_all_in : forall
  {A : Type}
  (P : A -> Prop)
  (s : t A)
  (x : A),
  for_all P s -> is_in x s -> P x.

(** If a predicate holds [for_all], then it holds for all in [peek_list]. *)
Parameter for_all_peek : forall
  {A : Type}
  (P : A -> Prop)
  (s : t A),
  for_all P s <-> List.Forall P (peek_list s).

End Signature.
