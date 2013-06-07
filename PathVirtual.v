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
(** Virtual paths. *)
Require Coq.Lists.List.
Require Coq.Strings.String.
Require ListAux.
Require ListMapWeak.
Require ListSetWeak.
Require MapWeak.
Require Names.
Require SetWeak.

Import ListAux.Notations.

Open Scope string_scope.
Open Scope list_scope.

(** A virtual path represents a path in the virtual filesystem.

Virtual paths are always absolute.

The concrete syntax of virtual paths is given by the following EBNF
grammar (where [name] indicates a string representing a 
valid [Names.name]):

<<
path = "/" , [ name , ("/" , name)* ] ;
>>

A virtual path is conceptually a list of [Names.name],
with the empty list representing the root directory. *)
Definition t := list Names.t.

Definition root : t := nil.

(** Some example virtual paths include: [/bin], and 
[/usr/bin/ps]. *)
Example bin        : t := Names.bin :: nil.

Example usr_bin_ps : t := Names.usr :: Names.bin :: Names.ps :: nil.

(** Because equality of [Names.name] is decidable, equality
    of [t] is too. *)
Theorem eq_decidable : forall (p0 p1 : t),
  {p0 = p1}+{~p0 = p1}.
Proof.
  apply List.list_eq_dec.
  apply Names.eq_decidable.
Qed.

(** The property of [p0] being an ancestor of [p1]. [p0] is an ancestor
of [p1] iff:
- [p0] is not equal to [p1], and
- [p0] is a prefix of [p1]
*)
Definition is_ancestor_of (p0 p1 : t) : Prop :=
  (p0 <> p1) /\ (ListAux.is_prefix p0 p1).

(** The property of [p0] being the parent of [p1]. [p0] is the parent
of [p1] iff:
- [p0] is an ancestor of [p1], and
- There exists some [x] such that [p0 @@ x = p1]
*)
Definition is_parent_of (p0 p1 : t) : Prop :=
  (is_ancestor_of p0 p1) /\ (exists x, p0 @@ x = p1).

(** The [root] path is an ancestor of any non-[root] path. *)
Theorem is_ancestor_of_root : forall (p : t),
  p <> root -> is_ancestor_of root p.
Proof.
  unfold is_ancestor_of.
  intros p Hn.
  split.
    apply not_eq_sym.
    assumption.
    induction p as [|px pr].
      contradict Hn; reflexivity.
      constructor.
Qed.

(** The [root] path has no ancestors. *)
Theorem is_ancestor_of_root_false : forall (p : t),
  ~is_ancestor_of p root.
Proof.
  unfold is_ancestor_of.
  induction p.
    intuition.
    intuition.
    inversion H1.
Qed.

(** The [root] path has no parent. *)
Theorem is_parent_of_root_false : forall (p : t),
  ~is_parent_of p root.
Proof.
  unfold root.
  unfold is_parent_of.
  induction p; intuition.
    inversion H1.
    contradict H. apply ListAux.append_element_not_equal.
    inversion H0.
    inversion H3.
Qed.

(** Iff a path has a single element, then its parent is the [root]. *)
Theorem is_parent_of_root_single : forall (x : Names.t),
  is_parent_of root (x :: nil).
Proof.
  unfold root.
  unfold is_parent_of.
  unfold is_ancestor_of.
  intro x.
  split.
  split.
    discriminate.
    constructor.
    exists x; reflexivity.
Qed.

(** Being an ancestor is decidable. *)
Theorem is_ancestor_of_decidable : forall (p0 p1 : t),
  {is_ancestor_of p0 p1}+{~is_ancestor_of p0 p1}.
Proof.
  unfold is_ancestor_of.
  intros p0 p1.
  destruct (eq_decidable p0 p1).
    right; rewrite e; intuition.
    destruct (ListAux.is_prefix_decidable Names.eq_decidable p0 p1).
      left; intuition.
      right; intuition.
Qed.

(** Being a parent is decidable. *)
Theorem is_parent_of_decidable : forall (p0 p1 : t),
  {is_parent_of p0 p1}+{~is_parent_of p0 p1}.
Proof.
  intros p0 p1.
  unfold is_parent_of   in *.
  unfold is_ancestor_of in *.
  destruct (is_ancestor_of_decidable p0 p1).
    destruct i.
    destruct (ListAux.append_element_decidable Names.eq_decidable p0 p1).
      left; intuition.
      right; intuition.
    unfold is_parent_of   in *.
    unfold is_ancestor_of in *.
    right; intuition.
Qed.

(** Being an ancestor is transitive. *)
Theorem is_ancestor_of_transitive : forall (p0 p1 p2 : t),
  is_ancestor_of p0 p1 -> is_ancestor_of p1 p2 -> is_ancestor_of p0 p2.
Proof.
Admitted.

(** The property of [p0] containing [p1]. The path [p0] is said to
contain [p1] iff:
- [p0 = p1], or
- [p0] is an ancestor of [p1] *)
Definition contains (p0 p1 : t) :=
  (p0 = p1) \/ (is_ancestor_of p0 p1).

(** [contains] is decidable. *)
Theorem contains_decidable : forall (p0 p1 : t),
  {contains p0 p1}+{~contains p0 p1}.
Proof.
  unfold contains.
  intros p0 p1.
  destruct (eq_decidable p0 p1).
  destruct (is_ancestor_of_decidable p0 p1).
    left; left; assumption.
    left; left; assumption.
  destruct (is_ancestor_of_decidable p0 p1).
    left; right; assumption.
    right; tauto.
Qed.

(** All paths contain themselves. *)
Theorem contains_self : forall (p : t),
  contains p p.
Proof.
  left; reflexivity.
Qed.

(** If [p] is contained by [root], then [p = root]. *)
Theorem contains_is_root : forall (p : t),
  contains p root -> p = root.
Proof.
  unfold contains.
  unfold is_ancestor_of.
  intros p Hc.
  induction p as [|ph pr].
    reflexivity.
    destruct Hc as [HL|HR].
      assumption.
      destruct HR as [HRL HRR].
        inversion HRR.
Qed.

(** Containment is transitive. *)
Theorem contains_trans : forall (p q r : t),
  contains p q -> contains q r -> contains p r.
Proof.
  intros p q r Hpq Hqr.
  unfold contains in *.
  unfold is_ancestor_of in *.
  destruct Hpq as [HpqL|HpqR].
    destruct Hqr as [HqrL|HqrR].
      left; apply (eq_trans HpqL HqrL).
      rewrite HpqL.
      right; assumption.
    destruct Hqr as [HqrL|HqrR].
      rewrite <- HqrL.
      right; assumption.
Admitted.

(** Paths can be "subtracted" to remove common prefixes. This
is useful for calculating the paths of files inside archives mounted
into a filesystem. As an example, if an archive [A] is mounted at
[/usr] and [A] contains the path [/bin/ps], then
[subtract /usr/bin/ps /usr = /bin/ps].

So, if [contains p1 p0], then subtraction removes the first
[length p1] elements of [p0]. *)
Definition subtract (p0 p1 : t) : t :=
  match contains_decidable p1 p0 with
  | left _  => List.skipn (length p1) p0
  | right _ => p0
  end.

(** As stated, [subtract /usr/bin/ps /usr = /bin/ps]. *)
Example subtract_usr : subtract usr_bin_ps (Names.usr :: nil) = Names.bin :: Names.ps :: nil.
Proof.
  compute.
  destruct contains_decidable as [Hc|Hnc].
    reflexivity.
    contradict Hnc.
      right; compute; intuition.
      inversion H.
      apply ListAux.IsPre_cons.
      constructor.
Qed.

(** Attempting to subtract [p1] from [p0] when [p1] does not contain [p0]
does nothing. *)
Theorem contains_subtract_false : forall (p0 p1 : t),
  ~contains p1 p0 -> subtract p0 p1 = p0.
Proof.
  intros p0 p1 Hna.
  unfold subtract.
  destruct (contains_decidable p1 p0).
    contradiction.
    reflexivity.
Qed.

(** If [p1] contains [p0], then subtracting [p1] from [p0] reduces
the length of [p0] by [length p1]. *)
Theorem contains_subtract_length : forall (p0 p1 : t),
  contains p1 p0 -> length (subtract p0 p1) = length p0 - length p1.
Proof.
  intros p0 p1.
  unfold subtract.
  destruct (contains_decidable p1 p0).
    intros; apply ListAux.skipn_length.
    intros; contradiction.
Qed.

(** If [p0 = p1], then [subtract p0 p1 = root]. *)
Theorem contains_subtract_is_root : forall (p0 p1 : t),
  p0 = p1 -> subtract p0 p1 = root.
Proof.
  intros p0 p1 H_eq.
  unfold subtract.
  rewrite H_eq.
  destruct (contains_decidable p1 p1) as [Hc|Hnc].
    apply ListAux.skipn_0.
    contradict Hnc.
    left; reflexivity.
Qed.

(** Subtracting anything from [root] results in [root]. *)
Theorem subtract_root : forall (p : t),
  subtract root p = root.
Proof.
  intros p.
  unfold subtract.
  destruct (contains_decidable p root).
    destruct p; reflexivity.
    reflexivity.
Qed.

(** Subtracting anything from [root] results in [root]. *)
Theorem subtract_from_root : forall (p : t),
   subtract root p = root.
 Proof.
   intros p.
   unfold subtract.
   destruct (contains_decidable p root).
     destruct p; reflexivity.
     reflexivity.
 Qed.

(** Subtracting [root] from [p] results in [p]. *)
Theorem subtract_root_from : forall p,
  subtract p root = p.
Proof.
  intros p.
  unfold subtract.
  destruct (contains_decidable root p); reflexivity.
Qed.

(** Subtracting [p] from itself results in [root]. *)
Theorem subtract_self : forall p,
  subtract p p = root.
Proof.
  intros p.
  unfold subtract.
  destruct (contains_decidable p p) as [Hc|Hnc].
    induction p.
      reflexivity.
      apply IHp.
      left; reflexivity.
    contradict Hnc.
      left; reflexivity.
Qed.

Theorem contains_subtract_id : forall (p0 p1 : t),
  contains p0 p1 -> p0 ++ (subtract p1 p0) = p1.
Proof.

Admitted.

(** The sequential enumeration of the ancestors of [p] is
a list of the ancestors of [p] starting with the most distant
ancestor first.

As an example, given a path [/usr/bin/ps], a sequential
enumeration of the ancestors would result in a list
[/ :: /usr :: /usr/bin :: nil].

The [Enumeration] module provides a function to calculate the
enumeration. *)
Module Type EnumerationSignature.
Parameter enumeration : t -> list t.

(** The [enumeration] of the [root] is empty. *)
Parameter enumeration_root : enumeration root = nil.

(** Therefore, if the enumeration of [p] is empty, then [p = root]. *)
Parameter enumeration_is_root : forall (p : t),
  enumeration p = nil -> p = root.

(** All paths returned by [enumeration] are ancestors of the original non-empty path. *)
Parameter enumeration_ancestors : forall (p q : t),
  p <> root -> (List.In q (enumeration p) <-> is_ancestor_of q p).
End EnumerationSignature.

(** The actual implementation of the [enumeration] function. *)
Module Enumeration <: EnumerationSignature.

Definition enumeration (e : t) :=
  match e with
  | nil    => nil
  | _ :: _ => ListAux.prefixes e
  end.

(** The [enumeration] of the [root] is empty. *)
Theorem enumeration_root :
  enumeration nil = nil.
Proof.
  reflexivity.
Qed.

(** Therefore, if the enumeration of [p] is empty, then [p = root]. *)
Theorem enumeration_is_root : forall (p : t),
  enumeration p = nil -> p = root.
Proof.
  induction p as [|ph pr].
    auto.
    intros.
    simpl in H.
    
Qed.

(** All paths returned by [enumeration] are ancestors of the original non-empty path. *)
Theorem enumeration_ancestors : forall (p q : t),
  p <> root -> (List.In q (enumeration p) <-> is_ancestor_of q p).
Proof.
  intros p q H.
  destruct p.
    contradict H; reflexivity.
    unfold enumeration.
    unfold is_ancestor_of.
    apply ListAux.prefixes_correct.
Qed.

End Enumeration.

(** As stated, [enumeration /usr/bin/ps = [/, /usr, /usr/bin]]. *)
Theorem enum_example : Enumeration.enumeration usr_bin_ps =
  nil :: (Names.usr :: nil) :: (Names.usr :: Names.bin :: nil) :: nil.
Proof.
  compute.
  reflexivity.
Qed.

(** A map with virtual paths as keys. *)
Module PathVirtualMapsKey : MapWeak.Parameters with Definition key := t.
  Definition key              := t.
  Definition key_eq_decidable := eq_decidable.
End PathVirtualMapsKey.

Module Maps := ListMapWeak.Make(PathVirtualMapsKey).

(** A finite set of virtual paths. *)
Module PathVirtualSetParameters : SetWeak.Parameters with Definition t := t.
  Definition t              := t.
  Definition t_eq_decidable := eq_decidable.
End PathVirtualSetParameters.

Module Sets := ListSetWeak.Make(PathVirtualSetParameters).
