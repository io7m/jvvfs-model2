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
(** Convenient [MapWeak] functions and theorems. *)
Require MapWeak.

(** The [MapWeakAux] module provides theorems that follow directly from those
defined in the [MapWeak] interface, but in forms more convenient for writing
functions without using tactics. *)
Module Make (M : MapWeak.Signature).

Theorem lookup_maps_to_some_right : forall {A : Type} (k : M.key) (x : A) (m : M.t A),
  M.lookup k m = Some x -> M.key_maps_to k x m.
Proof.
  intros.
  destruct (M.lookup_maps_to_some k x m).
  auto.
Qed.

Theorem lookup_maps_to_some_left : forall {A : Type} (k : M.key) (x : A) (m : M.t A),
  Some x = M.lookup k m -> M.key_maps_to k x m.
Proof.
  intros.
  destruct (M.lookup_maps_to_some k x m).
  auto.
Qed.

(** The [lookup] function, augmented with a proof that the result maps to the given
    key in the map. *)
Definition lookup_ex
  {A : Type}
  (k : M.key)
  (m : M.t A)
: option {x | M.key_maps_to k x m} :=
  match M.lookup k m as r
    return (M.lookup k m = r -> option {x | M.key_maps_to k x m})
  with
  | Some z => fun some =>
    Some (@exist A (fun x => M.key_maps_to k x m) z (lookup_maps_to_some_right k z m some))
  | None => fun _ =>
    None
  end eq_refl.

End Make.
