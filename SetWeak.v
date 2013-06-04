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
(** The [SetWeak] interface provides a simple set interface where the
only requirements on elements is the decidability of equality. *)

(** The [Parameters] module type contains the types of elements in sets. *)
Module Type Parameters.

  Parameter t              : Type.
  Parameter t_eq_decidable : forall (x y : t), {x = y}+{~x = y}.

End Parameters.

(** The [Signature] module type gives the actual interface.
It states that implementations will provide a type, [t], which
represents a set of values, and a collection of functions and theorems
for working with them. *)
Module Type Signature.

Parameter e : Type.

(** The type of sets containing values of type [e]. *)
Parameter t : Type.

(** The empty set. *)
Parameter empty : t.

(** A set with a single element. *)
Parameter singleton : e -> t.

(** The element [x] is in the set [s]. *)
Parameter is_in : forall (x : e) (s : t), Prop.

(** Whether or not an element [x] is in the set [s] is decidable. *)
Parameter is_in_decidable : forall (x : e) (s : t),
  {is_in x s}+{~is_in x s}.

(** Insert the element [x] into [s]. *)
Parameter insert : forall (x : e) (s : t), t.

(** Remove the element [x] from [s]. *)
Parameter remove : forall (x : e) (s : t), t.

(** The empty set contains no elements. *)
Parameter is_in_empty_false : forall (x : e),
  ~is_in x empty.

(** Inserting [x] into [s] means [x] is in [s]. *)
Parameter insert_is_in : forall (x : e) (s : t),
  is_in x (insert x s).

(** Inserting [x0] into [s] does not remove other elements. *)
Parameter insert_preserves_is_in : forall (x0 x1 : e) (s : t),
  x0 <> x1 -> is_in x0 s -> is_in x0 (insert x1 s).

(** Inserting [x0] into [s] does not insert other elements. *)
Parameter insert_preserves_is_in_false : forall (x0 x1 : e) (s : t),
  x0 <> x1 -> (~is_in x0 (insert x1 s) <-> ~is_in x0 s).

(** Removing [x] from [s] means [x] is not in [s]. *)
Parameter remove_is_in_false : forall (x : e) (s : t),
  ~is_in x (remove x s).

(** Removing [x0] from [s] does not remove other elements. *)
Parameter remove_preserves_is_in : forall (x0 x1 : e) (s : t),
  x0 <> x1 -> (is_in x0 (remove x1 s) <-> is_in x0 s).

(** If [x0] is not in [s], then it's still not in [s] after any removal. *)
Parameter remove_preserves_is_in_false : forall (x0 x1 : e) (s : t),
  ~is_in x0 s -> ~is_in x0 (remove x1 s).

(** If [x0 <> x1], and [x0] is not in [s] when [x1] is removed,
    then it was not in [s] before that. *)
Parameter remove_preserves_is_in_false_alt : forall (x0 x1 : e) (s : t),
  x0 <> x1 -> ~is_in x0 (remove x1 s) -> ~is_in x0 s.

(** The [singleton] set is the same as the [empty] set with one element inserted. *)
Parameter singleton_eq : forall (x : e),
  singleton x = insert x empty.

End Signature.
