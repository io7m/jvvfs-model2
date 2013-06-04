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
Require NonEmptyStack.

Open Scope list_scope.

(** A trivial implementation of the [NonEmptyStack] interface implemented with lists. *)
Module Make : NonEmptyStack.Signature.

Inductive nes (A : Type) :=
  | NES : forall (x : A), list A -> nes A.

Arguments NES [A] x _.

Definition t (A : Type) := nes A.

Definition singleton
  {A : Type}
  (x : A)
: t A := NES x nil.

Definition is_in {A : Type} (x : A) (s : t A) : Prop :=
  match s with
  | NES y ys => x = y \/ List.In x ys
  end.

Theorem is_in_decidable : forall
  {A : Type}
  (e : forall (x y : A), {x = y}+{~x = y})
  (x : A)
  (s : t A),
  {is_in x s}+{~is_in x s}.
Proof.
  intros A e x s.
  destruct s as [sh sr].
    destruct (e x sh) as [HL|HR].
      rewrite HL.
      left; left; reflexivity.
      destruct (List.In_dec e x sr) as [HInL|HInR].
        left; right; assumption.
        right; intro H; inversion H; contradiction.
Qed.

Definition push
  {A : Type}
  (x : A)
  (s : t A)
: t A :=
  match s with
  | NES y ys => NES x (y :: ys)
  end.

Definition pop
  {A : Type}
  (s : t A)
: A * (option (t A)) := 
  match s with
  | NES x nil       => (x, None)
  | NES x (y :: ys) => (x, Some (NES y ys))
  end.

Definition peek
  {A : Type}
  (s : t A)
: A :=
  match s with
  | NES x _ => x
  end.

Definition peek_list
  {A : Type}
  (s : t A)
: list A :=
  match s with
  | NES x xs => cons x xs
  end.

Definition is_singleton {A : Type} (s : t A) :=
  match s with
  | NES _ nil => True
  | NES _ _   => False
  end.

(** The [is_singleton] predicate is decidable. *)
Definition is_singleton_decidable : forall
  {A : Type}
  (s : t A),
  {is_singleton s}+{~is_singleton s}.
Proof.
  intros A s.
  destruct s as [x xs].
    destruct xs as [|y ys].
      left; exact I.
      right; auto.
Qed.

Definition singleton_is : forall {A : Type} (x : A),
  is_singleton (singleton x).
Proof.
  intros A x.
  exact I.
Qed.

Definition push_not_singleton : forall {A : Type} (x : A) (s : t A),
  ~is_singleton (push x s).
Proof.
  intros A x s.
  destruct s; auto.
Qed.

Definition peek_list_not_empty : forall {A : Type} (s : t A),
  peek_list s <> nil.
Proof.
  intros A s.
  destruct s; discriminate.
Qed.

Theorem eq_decidable : forall
  {A     : Type}
  (e     : forall (x y : A), {x = y}+{~x = y})
  (s0 s1 : t A),
  {s0 = s1}+{~s0 = s1}.
Proof.
  decide equality.
  apply (List.list_eq_dec e).
Qed.

Theorem push_in : forall {A : Type} (x : A) (s : t A),
  is_in x (push x s).
Proof.
  induction s.
  left; reflexivity.
Qed.

Theorem singleton_in : forall {A : Type} (x : A),
  is_in x (singleton x).
Proof.
  left; reflexivity.
Qed.

Theorem peek_list_in : forall
  {A : Type}
  (s : t A)
  (x : A),
  List.In x (peek_list s) <-> is_in x s.
Proof.
  intros A s x.
  unfold peek_list.
  split.
    destruct s as [sh sr].
    intros H_in.
    destruct H_in as [H_inL|H_inR].
      symmetry in H_inL.
      left; assumption.
      right; assumption.
    destruct s as [sh sr].
    intros H_in.
    destruct H_in as [H_inL|H_inR].
      symmetry in H_inL.
      left; assumption.
      right; assumption.
Qed.

Definition for_all
  {A : Type}
  (P : A -> Prop)
  (s : t A)
: Prop :=
  match s with
  | NES x xs => (P x) /\ (List.Forall P xs)
  end.

Theorem for_all_in : forall
  {A : Type}
  (P : A -> Prop)
  (s : t A)
  (x : A),
  for_all P s -> is_in x s -> P x.
Proof.
  intros A P s x Hfp Hin.
  induction s as [sh sr].
    destruct Hfp as [HfpL HfpR].
    destruct Hin as [HinL|HinR].
      rewrite HinL; assumption.
      destruct (List.Forall_forall P sr); auto.
Qed.

Theorem for_all_peek : forall
  {A : Type}
  (P : A -> Prop)
  (s : t A),
  for_all P s <-> List.Forall P (peek_list s).
Proof.
  intros A P s.
  unfold peek_list.
  split.
    intros H_for.
    induction s as [sh sr].
      destruct H_for as [HfL HfR].
      auto.
    intros H_lfor.
    induction s as [sh sr].
      inversion H_lfor.
      split; assumption.
Qed.

(** If [P] holds for all in [s], and [P -> Q], then [Q] holds for all in [s]. *)
Theorem for_all_implication : forall
  {A  : Type}
  (P  : A -> Prop)
  (Q  : A -> Prop)
  (PQ : forall x, P x -> Q x)
  (s  : t A),
  for_all P s -> for_all Q s.
Proof.
  intros A P Q PQ s H_fa.
  destruct s as [y ys].
    destruct H_fa as [H_faL H_faR].
    split.
      apply (PQ y H_faL).
      apply (@List.Forall_impl A P Q).
        apply PQ.
        assumption.
Qed.

(** If [P] holds for all in [s], and [P x], then [P] holds for all in [push x s]. *)
Theorem for_all_push : forall
  {A : Type}
  (P : A -> Prop)
  (s : t A)
  (x : A),
  for_all P s -> P x -> for_all P (push x s).
Proof.
  intros until s.
  destruct s as [y ys].
    intros.
    destruct H.
    simpl.
    split.
    assumption.
    auto.
Qed.

(** If [P] holds for [x], then it holds for the [singleton]. *)
Theorem for_all_singleton : forall
  {A : Type}
  (P : A -> Prop)
  (x : A),
  P x -> for_all P (singleton x).
Proof.
  intros A P x.
  simpl; auto.
Qed.

End Make.