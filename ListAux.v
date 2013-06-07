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
(** Functions and theorems about lists. *)
Require Coq.Lists.List.
Require Coq.Arith.Peano_dec.

Open Scope list_scope.

(** Add [x] to the end of [xs]. *)
Definition append_element
  {A  : Type}
  (xs : list A)
  (x  : A)
: list A := xs ++ (x :: nil).

Module Notations.
Infix "@@" := append_element
  (right associativity, at level 60) : list_scope.
End Notations.

Import Notations.

(** Appending an element increases the length of a list by [1]. *)
Theorem append_element_length : forall
  {A  : Type}
  (xs : list A)
  (x  : A),
  S (length xs) = length (append_element xs x).
Proof.
  intros A xs x.
  induction xs as [|xh xr].
    reflexivity.
    simpl; rewrite IHxr; reflexivity.
Qed.

Lemma cons_neq_injection_0 : forall
  {A     : Type}
  (xs ys : list A)
  (x     : A),
  x :: xs <> x :: ys -> xs <> ys.
Proof.
  intros A xs.
  induction xs as [|xh xr].
    destruct ys as [|yh yr].
      auto with *.
      discriminate.
    destruct ys as [|yh yr].
      discriminate.
      intros x H_neq.
      injection.
      intros H_xryr_eq H_xhyh_eq.
      rewrite H in H_neq.
      contradict H_neq.
      reflexivity.
Qed.

Lemma cons_neq_injection_1 : forall
  {A     : Type}
  (xs ys : list A)
  (x     : A),
  xs <> ys -> x :: xs <> x :: ys.
Proof.
  intros A xs ys x H_neq.
  injection. assumption.
Qed.

Theorem cons_neq_injection : forall
  {A     : Type}
  (xs ys : list A)
  (x     : A),
  xs <> ys <-> x :: xs <> x :: ys.
Proof.
  intros A xs ys x.
  split.
    apply cons_neq_injection_1.
    apply cons_neq_injection_0.
Qed.

(** A list with a non-nil appendage is not the original list. *)
Theorem append_not_equal : forall
  {A     : Type}
  (xs ys : list A),
  ys <> nil -> xs ++ ys <> xs.
Proof.
  intros A xs.
  induction xs.
    auto.
    destruct ys as [|y yr].
      auto.
      simpl. intros H_neq.
      apply cons_neq_injection_1.
      apply IHxs.
      assumption.
Qed.

(** A list with a non-nil appendage is not nil. *)
Theorem append_not_nil : forall
  {A     : Type}
  (xs ys : list A),
  ys <> nil -> xs ++ ys <> nil.
Proof.
  intros A xs.
  induction xs as [|x xr].
    auto.
    destruct ys as [|y yr].
      auto.
      simpl. intros H_neq.
        discriminate.
Qed.

(** A list with an element appended is not the original list. *)
Theorem append_element_not_equal : forall
  {A  : Type}
  (xs : list A)
  (x  : A),
  append_element xs x <> xs.
Proof.
  intros A xs x.
  unfold append_element.
  apply append_not_equal.
  discriminate.
Qed.

(** A tactic for solving goals involving existentials. *)
Ltac append_crush :=
  match goal with
    | [          |- ~ _   ] => intro
    | [H : ex _  |- _     ] => inversion H; clear H
    | [H : _ = _ |- _     ] => solve [inversion H]
    | [H : _ = _ |- _ = _ ] => solve [inversion H; reflexivity]
    | [H : _ = _ |- ex _  ] => solve [inversion H; eexists; simpl; reflexivity]
    | [H : ~ _   |- False ] => destruct H
    | [          |- ex _  ] => eexists; simpl; reflexivity
  end.

(** It's possible to prove whether or not there is some [zs] such that [xs ++ zs = ys]. *)
Theorem append_decidable : forall
  {A     : Type}
  (e     : forall (x y : A), {x = y}+{~x = y})
  (xs ys : list A),
  {exists zs, xs ++ zs = ys}+{~exists zs, xs ++ zs = ys}.
Proof.
  induction xs.
    left. append_crush.
    destruct ys.
      right; repeat append_crush.
      destruct (IHxs ys).
        clear IHxs.
        destruct (e a a0).
          left; rewrite e1; repeat append_crush.
          right; repeat append_crush.
          right; repeat append_crush.
Qed.

(** It's possible to prove whether or not there is some [z] such that [xs @@ zs = ys]. *)
Theorem append_element_decidable : forall
  {A     : Type}
  (e     : forall (x y : A), {x = y}+{~x = y})
  (xs ys : list A),
  {exists z, append_element xs z = ys}+{~exists z, append_element xs z = ys}.
Proof.
  unfold append_element.
  induction xs.
    destruct ys.
      right; repeat append_crush.
      destruct ys.
        left; exists a; reflexivity.
        right; repeat append_crush.
    destruct ys.
      right; repeat append_crush.
      destruct (IHxs ys).
        clear IHxs.
        destruct (e a a0).
          left; rewrite e1; repeat append_crush.
          right; repeat append_crush.
          right; repeat append_crush.
Qed.

(** The property of one list being a prefix of another. *)
Inductive is_prefix {A : Type} : list A -> list A -> Prop :=
  | IsPre_nil  : forall x xs,    is_prefix nil (x :: xs)
  | IsPre_cons : forall x xs ys, is_prefix xs ys -> is_prefix (x :: xs) (x :: ys).

(** Nothing is a prefix of [nil]. *)
Theorem is_prefix_nil_false : forall
  {A : Type}
  (xs : list A),
  ~is_prefix xs nil.
Proof.
  induction xs; (intro H; inversion H).
Qed.

(** With decidable equality on elements of [A], the
    [is_prefix] property is decidable. *)
Theorem is_prefix_decidable : forall
  {A     : Type}
  (e     : forall (x y : A), {x = y}+{~x = y})
  (xs ys : list A),
  {is_prefix xs ys}+{~is_prefix xs ys}.
Proof.
  intros A e xs.
  induction xs as [|x xr].
    destruct ys as [|y yr].
      right; intros Hc; inversion Hc.
      left; constructor.
    destruct ys as [|y yr].
      right; intros Hc; inversion Hc.
      destruct (IHxr yr) as [IHL|IHR].
        destruct (e x y) as [H_xy_eq|H_xy_neq].
          rewrite <- H_xy_eq.
          left; constructor; assumption.
          right; intros Hc; inversion Hc; contradiction.
          right; intros Hc; inversion Hc; contradiction.
Qed.

(** If [xs ++ x] is a prefix of [ys], then [xs] is a prefix of [ys]. *)
Theorem is_prefix_app : forall
  {A        : Type}
  (xs zs ys : list A),
  is_prefix (xs ++ zs) ys -> is_prefix xs ys.
Proof.
  intros A.
  induction xs as [|x xr].
    simpl; destruct zs as [|z zr].
      intros ys H; assumption.
      intros ys H.
      destruct ys as [|y yr].
        inversion H.
        constructor.
      simpl; destruct ys as [|y yr].
        intros Hc; inversion Hc.
        intros H_pre.
        inversion H_pre.
        constructor.
        apply (IHxr zs yr H0).
Qed.

(** If [append_element xs x] is a prefix of [ys], then [xs] is a prefix of [ys]. *)
Theorem is_prefix_append_element : forall
  {A     : Type}
  (xs ys : list A)
  (x     : A),
  is_prefix (append_element xs x) ys -> is_prefix xs ys.
Proof.
  intros until x.
  unfold append_element.
  intros.
  apply (is_prefix_app xs (x :: nil) ys H).
Qed.

(** Nothing is a prefix of itself. *)
Theorem is_prefix_self : forall
  {A  : Type}
  (xs : list A),
  ~is_prefix xs xs.
Proof.
  intros A.
  induction xs.
    intros Hc; inversion Hc.
    intros Hc; inversion Hc; contradiction.
Qed.

(** The property that [P] holds for any element of [xs]. *)
Inductive any {A : Type} (P : A -> Prop) : list A -> Prop :=
  | Any_here  : forall x xs, P x      -> any P (x :: xs)
  | Any_there : forall x xs, any P xs -> any P (x :: xs).

(* If [P] holds in [any P xs], then there is some [x] in [xs] such that [P x]. *)
Theorem any_exists : forall {A : Type} (P : A -> Prop) (xs : list A),
  any P xs -> exists x, List.In x xs /\ P x.
Proof.
  intros A P xs H_any.
  induction H_any.
    exists x.
      split.
        left; reflexivity.
        assumption.
    destruct IHH_any as [z Hz].
      destruct Hz as [HzL HzR].
      exists z.
        split.
          right; assumption.
          assumption.
Qed.

(** If [P] holds for some element of [xs], then it holds for [x :: xs]. *)
Lemma any_cons : forall
  {A  : Type}
  (P  : A -> Prop)
  (x  : A)
  (xs : list A),
  any P xs -> any P (x :: xs).
Proof.
  intros A P x xs H_any.
  induction H_any.
    apply Any_there.
    apply Any_here.
    assumption.
    apply Any_there.
    apply Any_there.
    assumption.
Qed.

(** If [P] is decidable, then [any P xs] is decidable. *)
Theorem any_decidable : forall
  {A  : Type}
  (P  : A -> Prop)
  (d  : forall x : A, {P x}+{~P x})
  (xs : list A),
  {any P xs}+{~any P xs}.
Proof.
  intros A P d xs.
  induction xs as [|xh xr].
    right; intros Hc; inversion Hc.
    destruct IHxr as [IHxrL|IHxrR].
      left; apply Any_there; assumption.
      destruct (d xh) as [H_decL|H_decR].
        left; apply Any_here; assumption.
        right; intros Hc; inversion Hc; contradiction.
Qed.

(** Produce all sub-lists of [xs] with ends equal to that of [xs]. *)
Fixpoint tails
  {A  : Type}
  (xs : list A)
: list (list A) :=
  cons xs (match xs with
    | nil       => nil
    | cons _ xs => tails xs
  end).

(** The [tails] function produces a list of length [S (length xs)] -
    a list of all the sublists of [xs] plus an empty list. *)
Theorem tails_count : forall
  {A  : Type}
  (xs : list A),
  length (tails xs) = S (length xs).
Proof.
  intros A xs.
  induction xs as [|x xr].
    reflexivity.
    simpl; rewrite IHxr; reflexivity.
Qed.

(** The [tails] of an empty list is list containing the empty list. *)
Theorem tails_nil_eq : forall {A : Type}, tails nil = (@nil A) :: nil.
Proof.
  reflexivity.
Qed.

(** The property that [xs] contains [ys]. *)
Definition contains
  {A     : Type}
  (xs ys : list A)
: Prop :=
  any (is_prefix ys) (tails xs).

(** The empty list never contains a non-empty list. *)
Theorem contains_empty_false : forall {A : Type} (y : A) (ys : list A),
  ~contains nil (y :: ys).
Proof.
  intros A y.
  induction ys; (intros Hc; inversion Hc; inversion H0; inversion H0).
Qed.

(* With decidable equality on elements of [A], [contains] is
   decidable. *)
Theorem contains_decidable : forall
  {A     : Type}
  (e     : forall (x y : A), {x = y}+{~x = y})
  (xs ys : list A),
  {contains xs ys}+{~contains xs ys}.
Proof.
  unfold contains.
  intros A e xs ys.
  apply any_decidable.
  apply (is_prefix_decidable e).
Qed.

(** If [ys] is a prefix of [xs], then [xs] contains [ys]. *)
Theorem is_prefix_contains : forall {A : Type} (ys xs : list A),
  is_prefix ys xs -> contains xs ys.
Proof.
  intros A.
  induction ys as [|y yr].
    destruct xs as [|x xr].
      intros H_c; inversion H_c.
      intros H_p; constructor; assumption.
    destruct xs as [|x xr].
      intros H_c; inversion H_c.
      intros H_p.
      inversion H_p.
      constructor.
      rewrite H2 in H_p.
      assumption.
Qed.

(** The last element of [xs], if any. *)
Fixpoint last
  {A  : Type}
  (xs : list A)
: option A :=
  match xs with
  | nil      => None
  | x :: nil => Some x
  | _ :: xs  => last xs
  end.

(** An empty list has no last element. *)
Theorem last_empty_none : forall {A : Type},
  last (@nil A) = @None A.
Proof.
  reflexivity.
Qed.

(** [cons] does not affect [last] for non-empty lists. *)
Lemma last_cons_0 : forall
  {A   : Type}
  (xs  : list A)
  (x y : A),
  last (x :: xs) = last (y :: x :: xs).
Proof.
  intros A xs x y.
  induction xs; reflexivity.
Qed.

(** [cons] does not affect [last] for non-empty lists. *)
Lemma last_cons_1 : forall
  {A  : Type}
  (xs : list A)
  (x  : A),
  xs <> nil -> last xs = last (x :: xs).
Proof.
  intros A xs x y.
  induction xs; (tauto; reflexivity).
Qed.

(** A non-empty list has a last element. *)
Theorem last_nonempty_some : forall
  {A  : Type}
  (xs : list A),
  xs <> nil -> exists x, last xs = Some x.
Proof.
  intros A xs Hn.
  induction xs as [|xh xr].
    tauto.
    destruct xr.
      exists xh; reflexivity.
      assert (a :: xr <> nil) as H_nn by discriminate.
      rewrite <- (last_cons_0 xr a xh).
      apply (IHxr H_nn).
Qed.

(** The last element of an appended list is the last element of the new list. *)
Theorem last_appended : forall
  {A     : Type}
  (xs ys : list A),
  ys <> nil -> last (xs ++ ys) = last ys.
Proof.
  induction xs.
    tauto.
    intros ys Hy.
    rewrite <- (IHxs ys Hy).
    rewrite <- List.app_comm_cons.
    rewrite (last_cons_1 (xs ++ ys) a).
    reflexivity.
    apply append_not_nil.
    assumption.
Qed.

(** An appended element is the last element of the new list. *)
Theorem last_element_appended : forall
  {A  : Type}
  (xs : list A)
  (y  : A),
  last (append_element xs y) = Some y.
Proof.
  unfold append_element.
  intros A xs y.
  rewrite last_appended.
  reflexivity.
  discriminate.
Qed.

Definition remove_last
  {A  : Type}
  (xs : list A)
: list A :=
  List.rev (List.tl (List.rev xs)).

Theorem remove_last_nil : forall {A : Type},
  remove_last (@nil A) = nil.
Proof.
  reflexivity.
Qed.

Theorem tail_length : forall
  {A  : Type}
  (xs : list A),
  xs <> nil -> length xs = S (length (List.tl xs)).
Proof.
  induction xs as [|xh xr].
    intros. contradict H; reflexivity.
    intros. reflexivity.
Qed.

Theorem remove_last_length : forall
  {A  : Type}
  (xs : list A),
  xs <> nil -> length xs = S (length (remove_last xs)).
Proof.
  induction xs as [|xh xr].
    intros. contradict H; reflexivity.
    intros.
      unfold remove_last.
      rewrite List.rev_length.
      rewrite <- tail_length.
      rewrite List.rev_length.
      reflexivity.
      simpl. auto with *.
Qed.

Fixpoint prefixes_including_self
  {A  : Type}
  (xs : list A)
: list (list A) :=
  nil :: (match xs with
    | nil       => nil
    | cons y ys => List.map (cons y) (prefixes_including_self ys)
    end).

Definition prefixes
  {A  : Type}
  (xs : list A)
: list (list A) :=
  remove_last (prefixes_including_self xs).

Theorem prefixes_nil : forall {A : Type},
  prefixes (@nil A) = nil.
Proof.
  reflexivity.
Qed.

Lemma in_tail_app : forall
  {A  : Type}
  (x  : A)
  (xs : list A),
  xs <> nil -> List.In x (List.tl (xs ++ (x :: nil))).
Proof.
  intros.
  induction xs as [|xh xr].
    contradict H; reflexivity.
    simpl. auto with *.
Qed.

Lemma map_not_nil : forall
  {A B : Type}
  (xs  : list A)
  (f   : A -> B),
  xs <> nil -> List.map f xs <> nil.
Proof.
  induction xs as [|xh xr].
    intros. contradict H; reflexivity.
    simpl. discriminate.
Qed.

Lemma map_cons_grow : forall
  {A  : Type}
  (x  : A)
  (xs : list (list A)),
  length xs <= length (List.map (cons x) xs).
Proof.
  induction xs as [|xh xr].
    simpl; auto.
    simpl. auto with *.
Qed.

Lemma rev_not_nil : forall
  {A  : Type}
  (xs : list A),
  xs <> nil -> List.rev xs <> nil.
Proof.
  induction xs as [|xh xr].
    intros. contradict H; reflexivity.
    intros. simpl. auto with *.
Qed.

Lemma prefixes_correct : forall
  {A     : Type}
  (ys xs : list A),
  ys <> nil -> (is_prefix xs ys <-> List.In xs (prefixes ys)).
Proof.

Admitted.

Theorem skipn_length : forall
  {A     : Type}
  (xs ys : list A),
  length (List.skipn (length ys) xs) = length xs - length ys.
Proof.
  induction xs as [|xh xr].
    destruct ys; reflexivity.
    destruct ys.
      reflexivity.
      apply IHxr.
Qed.

Theorem skipn_0 : forall
  {A  : Type}
  (xs : list A),
  List.skipn (length xs) xs = nil.
Proof.
  induction xs as [|xh xr].
    reflexivity.
    apply IHxr.
Qed.

(** The length of the empty list is 0. *)
Theorem length_nil : forall {A : Type}, length (@nil A) = 0.
Proof.
  reflexivity.
Qed.

(** The length of any list grows by 1 when an element is prepended. *)
Theorem length_cons : forall
  {A  : Type}
  (xs : list A)
  (x  : A),
  S (length xs) = length (x :: xs).
Proof.
  induction xs; reflexivity.
Qed.

(** A list with a nonzero length implies a non-empty list. *)
Theorem length_nonzero_implies : forall
  {A  : Type}
  (xs : list A)
  (n  : nat),
  length xs = S n -> xs <> nil.
Proof.
  induction xs; discriminate.
Qed.

(** An inductive predicate that [x] is in [xs]. *)
Inductive InP {A : Type} : A -> list A -> Prop :=
  | InP_Here  : forall {x   : A} {xs : list A}, InP x (x :: xs)
  | InP_There : forall {y x : A} {xs : list A}, InP x xs -> InP x (y :: xs).

(** Translation from [InP] to [List.In] *)
Theorem InP_In : forall
  {A  : Type}
  (x  : A)
  (xs : list A),
  InP x xs -> List.In x xs.
Proof.
  intros.
  induction H; auto with *.
Qed.

Definition sig_map
  {A   : Type}
  {P Q : A -> Prop}
  (f   : forall x, P x -> Q x)
  (s   : {x : A | P x})
: { x | Q x }.
Proof.
  induction s.
    exists x; apply (f x p).
Defined.

Definition InP_In_sig
  {A  : Type}
  (xs : list A)
: {x | InP x xs} -> {x | List.In x xs} :=
  sig_map (fun x => InP_In x xs).

(** A list with a proof that each element is in the list. *)
Fixpoint inP_list
  {A  : Type}
  (xs : list A)
: list {x : A | InP x xs}.
Proof.
  induction xs as [|xh xr].
    apply nil.
    apply (exist
      (fun (x : A) => InP x (xh :: xr))
       xh InP_Here ::
       List.map (sig_map (fun (x : A) (P : InP x xr) => InP_There P)) IHxr).
Defined.

Theorem inP_list_preserves_not_nil : forall
  {A : Type}
  (xs : list A),
  xs <> nil -> inP_list xs <> nil.
Proof.
  induction xs.
    simpl; auto.
    discriminate.
Qed.

Definition in_list
  {A : Type}
  (xs : list A)
: list {x : A | List.In x xs} :=
  List.map (InP_In_sig xs) (inP_list xs).

Theorem in_list_preserves_not_nil : forall
  {A : Type}
  (xs : list A),
  xs <> nil -> in_list xs <> nil.
Proof.
  induction xs.
    simpl; auto.
    discriminate.
Qed.

Theorem map_preserves_not_nil : forall
  {A B : Type}
  (xs  : list A)
  (f   : A -> B),
  xs <> nil -> List.map f xs <> nil.
Proof.
  intros A B.
  induction xs.
    auto.
    discriminate.
Qed.
