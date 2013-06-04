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
Require Stack.

(** A trivial implementation of the [Stack] interface implemented with lists. *)
Module Make : Stack.Signature.

Definition t (A : Type) := list A.

Definition empty (A : Type) := @nil A.

Definition push
  {A : Type}
  (x : A)
  (s : t A)
: t A := cons x s.

Definition pop
  {A : Type}
  (s : t A)
: option (A * t A) :=
  match s with
  | nil       => None
  | cons x xs => Some (x, xs)
  end.

Definition peek
  {A : Type}
  (s : t A)
: option A :=
  match s with
  | nil      => None
  | cons x _ => Some x
  end.

Definition peek_list
  {A : Type}
  (s : t A)
: list A := s.

Fixpoint map
  {A B : Type}
  (f   : A -> B)
  (s   : t A)
: t B :=
  match s with
  | nil       => nil
  | cons x xs => cons (f x) (map f xs)
  end.

Fixpoint size
  {A : Type}
  (s : t A)
: nat :=
  match s with
  | nil       => O
  | cons _ ys => S (size ys)
  end.

Theorem push_pop_inv : forall {A : Type} (x : A) (s : t A),
  pop (push x s) = Some (x, s).
Proof.
  reflexivity.
Qed.

Theorem push_peek : forall {A : Type} (x : A) (s : t A),
  peek (push x s) = Some x.
Proof.
  reflexivity.
Qed.

Theorem push_size : forall {A : Type} (x : A) (s : t A),
  size (push x s) = S (size s).
Proof.
  reflexivity.
Qed.

Theorem pop_empty : forall {A : Type},
  pop (@empty A) = None.
Proof.
  reflexivity.
Qed.

Theorem peek_empty : forall {A : Type},
  peek (@empty A) = None.
Proof.
  reflexivity.
Qed.

Theorem map_id : forall {A : Type} (f : A -> A) (s : t A),
  (forall x : A, f x = x) -> map f s = s.
Proof.
  intros A f s H_id.
  induction s as [|y ys].
    (* s = nil *)
    reflexivity.
    (* s = y :: ys *)
    simpl.
    rewrite H_id.
    rewrite IHys.
    reflexivity.
Qed.

Definition is_in {A : Type} (x : A) (s : t A) : Prop :=
  List.In x s.

Theorem is_in_decidable : forall
  {A : Type}
  (e : forall (x y : A), {x = y}+{~x = y})
  (x : A)
  (s : t A),
  {is_in x s}+{~is_in x s}.
Proof.
  apply List.In_dec.
Qed.

Theorem peek_list_empty : forall {A : Type},
  peek_list (@empty A) = nil.
Proof.
  reflexivity.
Qed.

Theorem peek_list_nil_is_empty : forall {A : Type} (s : t A),
  peek_list s = nil <-> s = @empty A.
Proof.
  intros A s.
  split.
    intros H.
    destruct s.
      reflexivity.
      inversion H.
    intros H.
    destruct s.
      reflexivity.
      inversion H.
Qed.

Theorem is_in_empty_false : forall {A : Type} (x : A),
  ~is_in x (@empty A).
Proof.
  auto.
Qed.

Theorem empty_decidable : forall (A : Type) (s : t A),
  {s = @empty A}+{~s = @empty A}.
Proof.
  intros A s.
  destruct s as [He|Hne].
    left; reflexivity.
    right.
      intro H.
      inversion H.
Qed.

Theorem eq_decidable : forall
  {A     : Type}
  (e     : forall (x y : A), {x = y}+{~x = y})
  (s0 s1 : t A),
  {s0 = s1}+{~s0 = s1}.
Proof.
  intros A e.
  apply (List.list_eq_dec e).
Qed.

Theorem is_in_nonempty : forall {A : Type} (x : A) (s : t A),
  is_in x s -> s <> (@empty A).
Proof.
  intros A x s Hin.
  induction s as [|sh sr].
    contradict Hin.
    discriminate.
Qed.

Definition for_all
  {A : Type}
  (P : A -> Prop)
  (s : t A)
: Prop := List.Forall P s.

End Make.
