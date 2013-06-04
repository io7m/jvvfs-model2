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

(** The property of [xs] being a prefix of [ys]. *)
Fixpoint is_prefix
  {A     : Type}
  (xs ys : list A)
: Prop :=
  match xs, ys with
  | nil       , _         => True
  | _         , nil       => False
  | cons x xs , cons y ys => (x = y /\ is_prefix xs ys)
  end.

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
    left; simpl; auto.
    destruct ys as [|y yr].
      right; simpl; auto.
      simpl; destruct (e x y) as [H_xy_eq|H_xy_neq].
        destruct (IHxr yr).
          left; apply conj; assumption.
          right; intuition.
        destruct (IHxr yr).
          right; intuition.
          right; intuition.
Qed.

(** Return [true] iff [xs] is a prefix of [ys]. *)
Fixpoint is_prefix_bool
  {A     : Type}
  (e     : forall (x y : A), {x = y}+{~x = y})
  (xs ys : list A)
: bool :=
  match xs, ys with
  | nil         , _           => true
  | _           , nil         => false
  | (cons x xs) , (cons y ys) =>
    match e x y with
    | left  _ => is_prefix_bool e xs ys
    | right _ => false
    end
  end.

Lemma is_prefix_bool_correct1 : forall
  {A     : Type}
  (e     : forall (x y : A), {x = y}+{~x = y})
  (xs ys : list A),
  is_prefix xs ys -> is_prefix_bool e xs ys = true.
Proof.
  intros A e xs.
  induction xs as [|x xrest].
    reflexivity.
    destruct ys as [|y yrest].
      intros H_pre; inversion H_pre.
      intros H_pre.
      destruct H_pre as [H_preL H_preR].
        rewrite <- H_preL.
        cut (is_prefix_bool e xrest yrest = true).
          intros H_ind.
          simpl; destruct (e x x) as [H_xx_eq|H_xx_neq].
            assumption.
            contradict H_xx_neq.
          reflexivity.
        apply IHxrest.
        assumption.
Qed.

Lemma is_prefix_bool_correct2 : forall
  {A     : Type}
  (e     : forall (x y : A), {x = y}+{~x = y})
  (xs ys : list A),
  is_prefix_bool e xs ys = true -> is_prefix xs ys.
Proof.
  intros A e xs.
  induction xs as [|x xrest].
    reflexivity.
    destruct ys as [|y yrest].
      intros H_pre; inversion H_pre.
      intros H_pre.
        simpl in *; destruct (e x y) as [H_xy_eq|H_xy_neq].
          apply conj.
            assumption.
            apply IHxrest; assumption.
          inversion H_pre.
Qed.

(** Proof that [is_prefix_bool] does determine if [xs] is a prefix of [ys]. *)
Theorem is_prefix_bool_correct : forall
  {A     : Type}
  (e     : forall (x y : A), {x = y}+{~x = y})
  (xs ys : list A),
  is_prefix xs ys <-> is_prefix_bool e xs ys = true.
Proof.
  intros.
  apply conj.
    apply is_prefix_bool_correct1.
    apply is_prefix_bool_correct2.
Qed.

(** If [xs ++ x] is a prefix of [ys], then [xs] is a prefix of [ys]. *)
Theorem is_prefix_app : forall
  {A        : Type}
  (xs zs ys : list A),
  is_prefix (xs ++ zs) ys -> is_prefix xs ys.
Proof.
  intros A.
  induction xs as [|x xr].
    reflexivity.
    destruct zs as [|z zr].
      rewrite List.app_nil_r.
      intros; assumption.
      destruct ys as [|y yr].
        auto.
        intros H_p.
        simpl in *; destruct H_p as [H_pL H_pR].
          split.
            assumption.
            apply (IHxr (z :: zr) yr).
            assumption.
Qed.

(** If [append_element xs x] is a prefix of [ys], then [xs] is a prefix of [ys]. *)
Theorem is_prefix_append_element : forall
  {A     : Type}
  (xs ys : list A)
  (x     : A),
  is_prefix (append_element xs x) ys -> is_prefix xs ys.
Proof.
  intros A.
  unfold append_element.
  induction xs as [|x xr].
    reflexivity.
    destruct ys as [|y yr].
      intuition.
        intros x0 H_p.
        simpl in *; destruct H_p as [H_pL H_pR].
          split.
            assumption.
            apply (IHxr yr x0).
            assumption.
Qed.

(** Everything is a prefix of itself. *)
Theorem is_prefix_self : forall
  {A  : Type}
  (xs : list A),
  is_prefix xs xs.
Proof.
  intros A.
  induction xs.
    exact I.
    simpl; split. reflexivity. assumption.
Qed.

(** No non-[nil] list is a prefix of [nil]. *)
Theorem is_prefix_nil_false : forall
  {A  : Type}
  (xs : list A),
  xs <> nil -> ~is_prefix xs nil.
Proof.
  intros A xs H_neq.
  induction xs.
    contradict H_neq; reflexivity.
    auto.
Qed.

(** If a list if a prefix of [nil], then the list is [nil]. *)
Theorem is_prefix_nil_eq : forall
  {A  : Type}
  (xs : list A),
  is_prefix xs nil -> xs = nil.
Proof.
  induction xs.
    intros; reflexivity.
    intros.
      simpl in *.
      inversion H.
Qed.

(** If [xs] is a prefix of [ys], then [x :: xs] is a prefix of [x :: ys]. *)
Theorem is_prefix_cons : forall
  {A     : Type}
  (xs ys : list A)
  (x     : A),
  is_prefix xs ys -> is_prefix (x :: xs) (x :: ys).
Proof.
  induction xs.
    simpl; auto.
    destruct ys.
      intros.
      inversion H.
      intros.
      destruct H as [HL HR].
        rewrite HL.
        split.
          reflexivity.
          split.
            reflexivity.
            assumption.
Qed.

(** The property that [P] holds for any element of [xs]. *)
Fixpoint any
  {A  : Type}
  (P  : A -> Prop)
  (xs : list A)
: Prop :=
  match xs with
  | nil       => False
  | cons x xs => P x \/ any P xs
  end.

(* If [P] holds in [any P xs], then there is some [x] in [xs] such that [P x]. *)
Theorem any_exists : forall {A : Type} (P : A -> Prop) (xs : list A),
  any P xs -> exists x, List.In x xs /\ P x.
Proof.
  intros A P.
  induction xs as [|xh xr].
    intro H_any; inversion H_any.
    simpl; intro H_any.
    destruct H_any as [H_anyL|H_anyR].
      exists xh.
        apply conj.
          left; reflexivity.
          assumption.
      assert (exists x : A, List.In x xr /\ P x) as H_ex.
        apply (IHxr H_anyR).
      destruct H_ex as [H_exL H_exR].
        destruct H_exR as [H_exRL H_exRR].
          exists H_exL.
            apply conj.
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
  intros A P x xs.
  induction xs as [|xh xr].
    intro Hc; inversion Hc.
    intro Hany. right; assumption.
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
    right; auto.
    destruct IHxr as [IHxrL|IHxrR].
      left; apply (any_cons P xh xr IHxrL).
      destruct (d xh) as [H_decL|H_decR].
        left; left; assumption.
        right; simpl; intuition.
Qed.

(** Apply [f] to all elements of [xs], returning [true] if [f] returns
    [true] for any element. *)
Fixpoint any_bool
  {A  : Type}
  (f  : A -> bool)
  (xs : list A)
: bool :=
  match xs with
  | nil       => false
  | cons x xs => orb (f x) (any_bool f xs)
  end.

(** If a function passed to [any] never returns [true], then [any]
    returns [false]. *)
Theorem any_bool_correct_0 : forall {A : Type} (xs : list A),
  any_bool (fun _ => false) xs = false.
Proof.
  intros A xs.
  induction xs.
    reflexivity.
    simpl; exact IHxs.
Qed.

(** If a function passed to [any] returns [true], then [any]
    returns [true]. *)
Theorem any_bool_correct_1 : forall {A : Type} (x : A) (xs : list A),
  any_bool (fun _ => true) (x :: xs) = true.
Proof.
  intros A x xs.
  induction xs.
    reflexivity.
    simpl; exact IHxs.
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
  induction ys; (compute; intuition).
Qed.

(** All lists contain the empty list. *)
Theorem contains_non_empty : forall {A : Type} (xs : list A),
  contains xs nil.
Proof.
  intros A.
  induction xs as [|x xr].
    left; intuition.
    left; exact I.
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
Theorem is_prefix_contains : forall {A : Type} (xs ys : list A),
  is_prefix ys xs -> contains xs ys.
Proof.
  intros A xs.
  induction ys as [|y yr].
    intros. apply contains_non_empty.
    intros H_pre.
      destruct xs as [|x xr].
        inversion H_pre.
        destruct H_pre as [H_preL H_preR].
        left. split.
          assumption.
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

Fixpoint prefixes'
  {A   : Type}
  (xs  : list A)
  (acc : list A)
: list (list A) :=
  match xs with
  | nil     => nil
  | x :: xr =>
    match xr with
    | nil => nil
    | _   =>
      let acc_new := acc ++ (x :: nil) in
        acc_new :: (prefixes' xr acc_new)
    end
  end.

Definition prefixes
  {A   : Type}
  (xs  : list A)
: list (list A) :=
  nil :: prefixes' xs nil.

Theorem prefixes_correct : forall
  {A     : Type}
  (xs ys : list A),
  List.In ys (prefixes xs) <-> ys <> xs /\ is_prefix ys xs.
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