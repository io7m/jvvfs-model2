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
(** Functions and theorems about strings. *)
Require ListAux.
Require Coq.Strings.Ascii.
Require Coq.Strings.String.

Open Scope string_scope.

(** The property of one string being a prefix of another. *)
Inductive is_prefix : String.string -> String.string -> Prop :=
  | IsPre_nil  : forall c s0,    is_prefix String.EmptyString (String.String c s0)
  | IsPre_cons : forall c s0 s1, is_prefix s0 s1 -> is_prefix (String.String c s0) (String.String c s1).

(** The [is_prefix] proposition is decidable. *)
Theorem is_prefix_decidable : forall (s0 s1 : String.string),
  {is_prefix s0 s1}+{~is_prefix s0 s1}.
Proof.
  induction s0 as [|s0c s0r].
    destruct s1 as [|s1c s1r].
      right; intros Hc; inversion Hc.
      left; constructor.
    destruct s1 as [|s1c s1r].
      right; intros Hc; inversion Hc.
      destruct (IHs0r s1r) as [IHL|IHR].
        destruct (Ascii.ascii_dec s0c s1c) as [H_c_eq|H_c_neq].
          rewrite <- H_c_eq.
          left; constructor; assumption.
          right; intros Hc; inversion Hc; contradiction.
          right; intros Hc; inversion Hc; contradiction.
Qed.

(** Produce all sub-strings of [s] with ends equal to that of [s], returning
    the largest first. *)
Fixpoint tails (s : String.string) : list String.string :=
  cons s (match s with
    | String.EmptyString => nil
    | String.String _ xs => tails xs
  end).

(** The property that [s0] contains [s1]. *)
Definition contains (s0 s1 : String.string) : Prop :=
  ListAux.any (is_prefix s1) (tails s0).

(** The empty string never contains a non-empty string. *)
Theorem contains_empty_false : forall (c : Ascii.ascii) (s1 : String.string),
  ~contains String.EmptyString (String.String c s1).
Proof.
  intros c.
  induction s1; (intros Hc; inversion Hc; inversion H0; inversion H0).
Qed.

(** [contains] is decidable. *)
Definition contains_decidable : forall (s0 s1 : String.string),
  {contains s0 s1}+{~contains s0 s1}.
Proof.
  intros s0 s1.
  unfold contains.
  apply ListAux.any_decidable.
  apply is_prefix_decidable.
Qed.
