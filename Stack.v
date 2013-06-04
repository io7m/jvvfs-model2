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
(** The [Stack] interface provides simple abstract stacks. *)
Module Type Signature.

(** The type of stacks containing values of type [A]. *)
Parameter t : forall (A : Type), Type.

(** The empty stack. *)
Parameter empty : forall (A : Type), t A.

(** Whether or not a stack is empty is decidable. *)
Parameter empty_decidable : forall (A : Type) (s : t A),
  {s = @empty A}+{~s = @empty A}.

(** Push the value [x] to the stack [s]. *)
Parameter push : forall {A : Type} (x : A) (s : t A), t A.

(** Pop a value from the stack [s]. *)
Parameter pop : forall {A : Type} (s : t A), option (A * t A).

(** Peek at the value on top of the stack [s]. *)
Parameter peek : forall {A : Type} (s : t A), option A.

(** View the stack [s] as a list of elements. The first element
    of the list represents the top of the stack. *)
Parameter peek_list : forall {A : Type} (s : t A), list A.

(** The empty stack results in an empty list. *)
Parameter peek_list_empty : forall {A : Type},
  peek_list (@empty A) = nil.

(** An empty list implies an empty stack. *)
Parameter peek_list_nil_is_empty : forall {A : Type} (s : t A),
  peek_list s = nil <-> s = @empty A.

(** Map [f] over each value in the stack [s]. *)
Parameter map : forall {A B : Type} (f : A -> B) (s : t A), t B.

(** Return the number of elements in [s]. *)
Parameter size : forall {A : Type} (s : t A), nat.

(** Popping a value from the [empty] stack returns [None]. *)
Parameter pop_empty : forall {A : Type},
  pop (@empty A) = None.

(** Peeking at the [empty] stack returns [None]. *)
Parameter peek_empty : forall {A : Type},
  peek (@empty A) = None.

(** Pushing and popping a value results in the original stack. *)
Parameter push_pop_inv : forall {A : Type} (x : A) (s : t A),
  pop (push x s) = Some (x, s).

(** Pushing and peeking a value results in the pushed value. *)
Parameter push_peek : forall {A : Type} (x : A) (s : t A),
  peek (push x s) = Some x.

(** Pushing a value increases the size of [s] by [1]. *)
Parameter push_size : forall {A : Type} (x : A) (s : t A),
  size (push x s) = S (size s).

(** Applying the identity function to [s] results in [s]. *)
Parameter map_id : forall {A : Type} (f : A -> A) (s : t A),
  (forall x : A, f x = x) -> map f s = s.

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

(** Nothing is in the empty stack. *)
Parameter is_in_empty_false : forall {A : Type} (x : A), ~is_in x (@empty A).

(** If [x] is in [s], then [s] is not empty. *)
Parameter is_in_nonempty : forall {A : Type} (x : A) (s : t A),
  is_in x s -> s <> (@empty A).

(** With decidable equality of elements, equality of stacks is decidable. *)
Parameter eq_decidable : forall
  {A     : Type}
  (e     : forall (x y : A), {x = y}+{~x = y})
  (s0 s1 : t A),
  {s0 = s1}+{~s0 = s1}.

(** Predicates that hold for all elements of [s]. *)
Parameter for_all : forall
  {A : Type}
  (P : A -> Prop)
  (s : t A), Prop.

End Signature.
