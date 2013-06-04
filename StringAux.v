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

(** The property of [s0] being a prefix of [s1]. *)
Fixpoint is_prefix (s0 s1 : String.string) : Prop :=
  match s0, s1 with
  | String.EmptyString   , _                    => True
  | _                    , String.EmptyString   => False
  | (String.String x xs) , (String.String y ys) => (x = y /\ is_prefix xs ys)
  end.

(** Return [true] if [s0] contains [s1]. *)
Fixpoint is_prefix_bool (s0 s1 : String.string) : bool :=
  match s0, s1 with
  | String.EmptyString   , _                    => true
  | _                    , String.EmptyString   => false
  | (String.String x xs) , (String.String y ys) =>
    match Ascii.ascii_dec x y with
    | left  _ => is_prefix_bool xs ys
    | right _ => false
    end
  end.

(** The [is_prefix] proposition is decidable. *)
Theorem is_prefix_decidable : forall (s0 s1 : String.string),
  {is_prefix s0 s1}+{~is_prefix s0 s1}.
Proof.
  intros s0.
  induction s0 as [|c0 s0r].
    left; simpl; auto.
    destruct s1 as [|c1 s1r].
      right; simpl; auto.
      simpl; destruct (Ascii.ascii_dec c0 c1) as [H_c0c1_eq|H_c0c1_neq].
        destruct (IHs0r s1r).
          left; apply conj; assumption.
          right; intuition.
        destruct (IHs0r s1r).
          right; intuition.
          right; intuition.
Qed.

Lemma is_prefix_bool_correct1 : forall (s0 s1 : String.string),
  is_prefix s0 s1 -> is_prefix_bool s0 s1 = true.
Proof.
  intros s0.
  induction s0 as [|c0 s0r].
    reflexivity.
    destruct s1 as [|c1 s1r].
      intros H_pre; inversion H_pre.
      intros H_pre.
      destruct H_pre as [H_preL H_preR].
        rewrite <- H_preL.
        cut (is_prefix_bool s0r s1r = true).
          intros H_ind.
          simpl; destruct (Ascii.ascii_dec c0 c0) as [H_c0c0_eq|H_c0c0_neq].
            assumption.
            contradict H_c0c0_neq.
          reflexivity.
        apply IHs0r.
        assumption.
Qed.

Lemma is_prefix_bool_correct2 : forall (s0 s1 : String.string),
  is_prefix_bool s0 s1 = true -> is_prefix s0 s1.
Proof.
  intros s0.
  induction s0 as [|c0 s0r].
    reflexivity.
    destruct s1 as [|c1 s1r].
      intros H_pre; inversion H_pre.
      intros H_pre.
        simpl in *; destruct (Ascii.ascii_dec c0 c1) as [H_c0c1_eq|H_c0c1_neq].
          apply conj.
            assumption.
            apply IHs0r; assumption.
          inversion H_pre.
Qed.

(** Proof that [is_prefix_bool] does determine if [s0] is a prefix of [s1]. *)
Theorem is_prefix_bool_correct : forall (s0 s1 : String.string),
  is_prefix s0 s1 <-> is_prefix_bool s0 s1 = true.
Proof.
  intros.
  apply conj.
    apply is_prefix_bool_correct1.
    apply is_prefix_bool_correct2.
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
  induction s1; (compute; intuition).
Qed.

(** All strings contain the empty string. *)
Theorem contains_non_empty : forall (s0 : String.string),
  contains s0 String.EmptyString.
Proof.
  intros s0.
  induction s0.
    left; intuition.
    left; exact I.
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

(** Return [true] if [s0] contains [s1]. *)
Definition contains_bool (s0 s1 : String.string) : bool :=
  ListAux.any_bool (is_prefix_bool s1) (tails s0).
