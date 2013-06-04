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
Require Coq.Lists.List.

(** The [MapWeak] interface provides a simple map interface where the
only requirements on keys is the decidability of equality. *)

(** The [Parameters] module type contains the types of keys in maps. *)
Module Type Parameters.

Parameter key              : Type.
Parameter key_eq_decidable : forall (x y : key), {x = y}+{~x = y}.

End Parameters.

(** The [Signature] module type gives the actual interface.
It states that implementations will provide a type, [t], which
represents a set of mappings between keys and values,
and a collection of functions and theorems for working with them. *)
Module Type Signature.

Parameter key : Type.

(** The type of maps containing values of type [A]. *)
Parameter t : forall (A : Type), Type.

(** The key [k] maps to [x] in the map [m]. *)
Parameter key_maps_to : forall {A : Type} (k : key) (x : A) (m : t A), Prop.

(** The key [k] is in the map [m]. *)
Parameter key_in : forall {A : Type} (k : key) (m : t A), Prop.

(** [key_maps_to] implies [key_in]. *)
Parameter key_maps_to_in : forall {A : Type} (k : key) (x : A) (m : t A),
  key_maps_to k x m -> key_in k m.

(** ~[key_in k m] implies that there is no [x] such that [key_maps_to k x m]. *)
Parameter key_in_false_maps_to_any : forall {A : Type} (k : key) (x : A) (m : t A),
  ~key_in k m -> ~key_maps_to k x m.

(** If [k0 = k1], [key_maps_to k0 x0 m], and [key_maps_to k1 x1 m], then [x0 = x1]. *)
Parameter key_maps_to_eq_value : forall {A : Type} (k0 k1 : key) (x0 x1 : A) (m : t A),
  k0 = k1 -> key_maps_to k0 x0 m -> key_maps_to k1 x1 m -> x0 = x1.

(** If two keys map to different values, then the keys must be different:
    If [x0 <> x1], [key_maps_to k0 x0 m], and [key_maps_to k1 x1 m], then [k0 <> k1]. *)
Parameter key_maps_to_neq_keys : forall {A : Type} (k0 k1 : key) (x0 x1 : A) (m : t A),
  x0 <> x1 -> key_maps_to k0 x0 m -> key_maps_to k1 x1 m -> k0 <> k1.

(** With decidable equality of [A], whether or not [k] maps to [x] is decidable. *)
Parameter key_maps_to_decidable : forall
  {A : Type}
  (k : key)
  (x : A)
  (m : t A)
  (e : forall (x y : A), {x = y}+{~x = y}),
  {key_maps_to k x m}+{~key_maps_to k x m}.

(** If [x <> y] and [key_maps_to k x m], then [k] does not map to [y]. *)
Parameter key_maps_to_not : forall {A : Type} (k : key) (x y : A) (m : t A),
  x <> y -> key_maps_to k x m -> ~key_maps_to k y m.

(** An empty map. *)
Parameter empty : forall {A : Type}, t A.

(** There are no keys in the empty map. *)
Parameter empty_in_false : forall {A : Type} (k : key),
  ~key_in k (@empty A).

(** No [k] maps to [x] in the empty map. *)
Parameter empty_maps_to_false : forall {A : Type} (k : key) (x : A),
  ~key_maps_to k x (@empty A).

(** Whether or not [m] is empty is decidable. *)
Parameter empty_decidable : forall {A : Type} (m : t A),
  {m = empty}+{~m = empty}.

(** Update the map [m] with a mapping of [k] to [x]. *)
Parameter insert : forall {A : Type} (k : key) (x : A) (m : t A), t A.

(** Inserting a key updates a mapping. *)
Parameter insert_maps_to : forall {A : Type} (k : key) (x : A) (m : t A),
  key_maps_to k x (insert k x m).

(** Inserting a key preserves all other mappings. *)
Parameter insert_preserves_maps_to : forall {A : Type} (k0 k1 : key) (x0 x1 : A) (m : t A),
  k0 <> k1 -> key_maps_to k0 x0 m -> key_maps_to k0 x0 (insert k1 x1 m).

(** If [k0 <> k1], and [k0] doesn't map to [x], then it still doesn't map to [x] after [k1] is inserted. *)
Parameter insert_preserves_not_maps_to : forall {A : Type} (k0 k1 : key) (x0 x1 : A) (m : t A),
  k0 <> k1 -> ~key_maps_to k0 x0 m -> ~key_maps_to k0 x0 (insert k1 x1 m).

(** Inserting a key doesn't insert anything else. *)
Parameter insert_preserves_not_in : forall {A : Type} (k0 k1 : key) (x : A) (m : t A),
  k0 <> k1 -> ~key_in k0 m -> ~key_in k0 (insert k1 x m).

(** Remove any mapping of [k] in the map [m]. *)
Parameter remove : forall {A : Type} (k : key) (m : t A), t A.

(** Removing a key eliminates a mapping. *)
Parameter remove_not_maps_to : forall {A : Type} (k : key) (x : A) (m : t A),
  ~key_maps_to k x (remove k m).

(** Removing a key preserves all other mappings. *)
Parameter remove_preserves_maps_to : forall {A : Type} (k0 k1 : key) (x : A) (m : t A),
  k0 <> k1 -> key_maps_to k0 x m -> key_maps_to k0 x (remove k1 m).

(** Removing a key preserves all other mappings. *)
Parameter remove_preserves_maps_to_alt : forall {A : Type} (k0 k1 : key) (x : A) (m : t A),
  k0 <> k1 -> key_maps_to k0 x (remove k1 m) -> key_maps_to k0 x m.

(** If [k0] doesn't map to [x], then it still doesn't map to [x] after a key is removed. *)
Parameter remove_preserves_not_maps_to : forall {A : Type} (k0 k1 : key) (x : A) (m : t A),
  ~key_maps_to k0 x m -> ~key_maps_to k0 x (remove k1 m).

(** If [k0 <> k1], and [k0] does not map to [x] after [k1] is removed,
    then [k0] did not map to [x] before. *)
Parameter remove_preserves_not_maps_to_alt : forall {A : Type} (k0 k1 : key) (x : A) (m : t A),
  k0 <> k1 -> ~key_maps_to k0 x (remove k1 m) -> ~key_maps_to k0 x m.

(** Removing a key eliminates a mapping. *)
Parameter remove_not_in : forall {A : Type} (k : key) (m : t A),
  ~key_in k (remove k m).

(** Removing a key preserves all other mappings. *)
Parameter remove_preserves_in : forall {A : Type} (k0 k1 : key) (m : t A),
  k0 <> k1 -> key_in k0 m -> key_in k0 (remove k1 m).

(** Removing a key preserves all other mappings. *)
Parameter remove_preserves_in_alt : forall {A : Type} (k0 k1 : key) (m : t A),
  k0 <> k1 -> key_in k0 (remove k1 m) -> key_in k0 m.

(** A key that is not present is still not present after a removal. *)
Parameter remove_preserves_not_in : forall {A : Type} (k0 k1 : key) (m : t A),
  ~key_in k0 m -> ~key_in k0 (remove k1 m).

(** If [k0 <> k1], and [k0] is not in a map after [k1] is removed,
    then [k0] was not in the map before. *)
Parameter remove_preserves_not_in_alt : forall {A : Type} (k0 k1 : key) (m : t A),
  k0 <> k1 -> ~key_in k0 (remove k1 m) -> ~key_in k0 m.

(** Retrieve the value, if any, associated with [k]. *)
Parameter lookup : forall {A : Type} (k : key) (m : t A), option A.

(** [k] maps to [x] iff looking up [k] returns [x]. *)
Parameter lookup_maps_to_some : forall {A : Type} (k : key) (x : A) (m : t A),
  key_maps_to k x m <-> lookup k m = Some x.

(** If [k] is not in [m], then looking up [k] returns [None]. *)
Parameter lookup_not_in_none : forall {A : Type} (k : key) (m : t A),
  ~key_in k m <-> lookup k m = None.

(** A list of all keys in the map [m]. *)
Parameter keys : forall {A : Type} (m : t A), list key.

(** A key [k] is in the list of keys iff it is in [m]. *)
Parameter keys_in : forall {A : Type} (m : t A) (k : key),
  key_in k m = List.In k (keys m).

(** A key [k] is not in the list of keys iff it is not in [m]. *)
Parameter keys_in_false : forall {A : Type} (m : t A) (k : key),
  (~key_in k m) = (~List.In k (keys m)).

(** The [empty] map has an empty list of [keys]. *)
Parameter keys_empty : forall {A : Type} (m : t A),
  keys m = nil <-> m = empty.

(** Predicates that hold for all values in [m]. *)
Parameter for_all_values : forall
  {A : Type}
  (P : A -> Prop)
  (m : t A), Prop.

(** [for_all_values] trivially holds for [empty]. *)
Parameter for_all_values_empty : forall
  {A : Type}
  (P : A -> Prop),
  for_all_values P empty.

(** [for_all_values] holds for [remove]. *)
Parameter for_all_values_remove : forall
  {A : Type}
  (P : A -> Prop)
  (m : t A)
  (k : key)
  (x : A),
  for_all_values P m -> for_all_values P (remove k m).

(** [for_all_values] holds on [insert] if [P] holds for the inserted value. *)
Parameter for_all_values_insert : forall
  {A : Type}
  (P : A -> Prop)
  (m : t A)
  (k : key)
  (x : A),
  P x -> for_all_values P m -> for_all_values P (insert k x m).

(** If [P] holds for all values, and [k] maps to [x], then [P x]. *)
Parameter for_all_values_maps : forall
  {A : Type}
  (P : A -> Prop)
  (m : t A)
  (k : key)
  (x : A),
  for_all_values P m -> key_maps_to k x m -> P x.

(** Predicates that hold for all mappings in [m]. *)
Parameter for_all_mappings : forall
  {A : Type}
  (P : key -> A -> Prop)
  (m : t A), Prop.

(** [for_all_mappings] trivially holds for [empty]. *)
Parameter for_all_mappings_empty : forall
  {A : Type}
  (P : key -> A -> Prop),
  for_all_mappings P empty.

(** [for_all_mappings] holds for [remove]. *)
Parameter for_all_mappings_remove : forall
  {A : Type}
  (P : key -> A -> Prop)
  (m : t A)
  (k : key),
  for_all_mappings P m -> for_all_mappings P (remove k m).

(** [for_all_mappings] holds on [insert] if [P] holds for the inserted value. *)
Parameter for_all_mappings_insert : forall
  {A : Type}
  (P : key -> A -> Prop)
  (m : t A)
  (k : key)
  (x : A),
  P k x -> for_all_mappings P m -> for_all_mappings P (insert k x m).

(** If [P] holds for all values, and [k] maps to [x], then [P x]. *)
Parameter for_all_mappings_maps : forall
  {A : Type}
  (P : key -> A -> Prop)
  (m : t A)
  (k : key)
  (x : A),
  for_all_mappings P m -> key_maps_to k x m -> P k x.

(** Predicates that hold for all keys in [m]. *)
Parameter for_all_keys : forall
  {A : Type}
  (P : key -> Prop)
  (m : t A), Prop.

(** [for_all_keys] trivially holds for [empty]. *)
Parameter for_all_keys_empty : forall
  {A : Type}
  (P : key -> Prop),
  for_all_keys P (@empty A).

End Signature.
