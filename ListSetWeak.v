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
Require SetWeak.

(** A trivial and extremely inefficient implementation of the [SetWeak]
interface implemented with lists. *)
Module Make (P : SetWeak.Parameters) : SetWeak.Signature with Definition e := P.t.

Definition e := P.t.

Definition t := list e.

Definition singleton (x : e) := cons x nil.

Fixpoint is_in
  (x : e)
  (s : t)
: Prop :=
  match s with
  | nil       => False
  | cons y ys => (x = y) \/ (x <> y /\ is_in x ys)
  end.

Theorem is_in_decidable : forall (x : e) (s : t),
  {is_in x s}+{~is_in x s}.
Proof.
  induction s as [|sh sr].
    right; auto.
    destruct IHsr as [IHL|IHR].
      destruct (P.t_eq_decidable x sh) as [H_eq|H_neq].
        rewrite H_eq.
        left; left; reflexivity.
        simpl; auto.
      destruct (P.t_eq_decidable x sh) as [H_eq|H_neq].
        rewrite H_eq.
        left; left; reflexivity.
        simpl in *; intuition.
Qed.

Fixpoint remove
  (x : e)
  (s : t)
: t :=
  match s with
  | nil       => nil
  | cons y ys =>
    match P.t_eq_decidable x y with
    | left _  => remove x ys
    | right _ => cons y (remove x ys)
    end
  end.

Fixpoint insert
  (x : e)
  (s : t)
: t := cons x (remove x s).

Definition empty := @nil e.

Theorem remove_is_in_false : forall (x : e) (s : t),
  ~is_in x (remove x s).
Proof.
  intros x s.
  induction s as [|y ys].
    (* s = nil *)
    simpl; auto.
    (* s = y :: ys *)
    simpl; destruct (P.t_eq_decidable x y) as [H_xy_eq|H_xy_neq].
      (* x = y *)
      assumption.
      (* x <> y *)
      simpl.
      unfold not.
      intros H_contra_goal.
      destruct H_contra_goal as [H_cg_L|H_cg_R].
        contradict H_xy_neq; assumption.
        destruct H_cg_R as [H_cg_RL H_cg_RR].
          auto.
Qed.

Theorem remove_preserves_is_in : forall (x0 x1 : e) (s : t),
  x0 <> x1 -> (is_in x0 (remove x1 s) <-> is_in x0 s).
Proof.
  intros x0 x1 s H_x0x1_neq.
  apply conj.
    intros H_in_remove.
    induction s as [|y ys].
      (* s = nil *)
      simpl; auto.
      (* s = y :: ys *)
      simpl in *. destruct (P.t_eq_decidable x1 y) as [H_x1y_eq|H_x1y_neq].
        (* x1 = y *)
        right; apply conj.
          rewrite H_x1y_eq in H_x0x1_neq.
          assumption.
          apply (IHys H_in_remove).
        (* x1 <> y *)
        destruct H_in_remove as [H_in_remove_L|H_in_remove_R].
          left; assumption.
          right; apply conj.
            destruct H_in_remove_R as [H_in_remove_RL H_in_remove_RR].
              assumption.
            destruct H_in_remove_R as [H_in_remove_RL H_in_remove_RR].
              apply (IHys H_in_remove_RR).

    intros H_in_remove.
    induction s as [|y ys].
      (* s = nil *)
      simpl; auto.
      (* s = y :: ys *)
      simpl in *. destruct (P.t_eq_decidable x1 y) as [H_x1y_eq|H_x1y_neq].
        (* x1 = y *)
        destruct H_in_remove as [H_in_remove_L|H_in_remove_R].
          contradict H_x0x1_neq.
            rewrite H_in_remove_L.
            rewrite H_x1y_eq.
            reflexivity.
          destruct H_in_remove_R as [H_in_remove_RL H_in_remove_RR].
            apply (IHys H_in_remove_RR).
        (* x1 <> y *)
        simpl; destruct H_in_remove as [H_in_remove_L|H_in_remove_R].
          left; assumption.
          right; apply conj.
            destruct H_in_remove_R as [H_in_remove_RL H_in_remove_RR].
              assumption.
            destruct H_in_remove_R as [H_in_remove_RL H_in_remove_RR].
              apply (IHys H_in_remove_RR).
Qed.

Lemma not_in_cons_0 : forall (x0 x1 : e) (s : t),
  x0 <> x1 -> ~is_in x0 (cons x1 s) -> ~is_in x0 s.
Proof.
  intros x0 x1 s H_neq H_not_in.
  simpl in *; intuition.
Qed.

Lemma not_in_cons_1 : forall (x0 x1 : e) (s : t),
  x0 <> x1 -> ~is_in x0 s -> ~is_in x0 (cons x1 s).
Proof.
  intros x0 x1 s H_neq H_not_in.
  simpl in *; intuition.
Qed.

Lemma remove_preserves_is_in_false : forall (x0 x1 : e) (s : t),
  ~is_in x0 s -> ~is_in x0 (remove x1 s).
Proof.
  intros x0 x1 s H_not_in.
  destruct (P.t_eq_decidable x0 x1) as [H_x0x1_eq|H_x0x1_neq].
    rewrite H_x0x1_eq.
    apply remove_is_in_false.
    induction s as [|sh sr].
      auto.
      simpl; destruct (P.t_eq_decidable x1 sh) as [H_x1sh_eq|H_x1sh_neq].
        rewrite <- H_x1sh_eq in H_not_in.
        assert (~is_in x0 sr) as H_not_in_rest.
          apply (not_in_cons_0 x0 x1 sr H_x0x1_neq H_not_in).
        apply (IHsr H_not_in_rest).
        simpl in *.
        intuition.
Qed.

Theorem remove_preserves_is_in_false_alt : forall (x0 x1 : e) (s : t),
  x0 <> x1 -> ~is_in x0 (remove x1 s) -> ~is_in x0 s.
Proof.
  intros x0 x1 s H_neq H_not_in.
  induction s as [|sh sr].
    simpl; auto.
    simpl in H_not_in.
    destruct (P.t_eq_decidable x1 sh) as [H_x1sh_eq|H_x1sh_neq].
      assert (~is_in x0 sr) by (apply (IHsr H_not_in)).
      rewrite <- H_x1sh_eq.
      apply (not_in_cons_1 x0 x1 sr H_neq H).
      simpl in *; intuition.
Qed.

Theorem is_in_empty_false : forall (x : e), ~is_in x empty.
Proof.
  intros x.
  compute; auto.
Qed.

Theorem insert_is_in : forall (x : e) (s : t),
  is_in x (insert x s).
Proof.
  intros x s.
  induction s as [|y ys].
    (* s = nil *)
    simpl; auto.
    (* s = y :: ys *)
    simpl; left; reflexivity.
Qed.

Theorem insert_preserves_is_in : forall (x0 x1 : e) (s : t),
  x0 <> x1 -> is_in x0 s -> is_in x0 (insert x1 s).
Proof.
  intros x0 x1 s H_x0x1_neq H_x0_in.
  induction s as [|y ys].
    (* s = nil *)
    simpl; auto.
    (* s = y :: ys *)
    simpl in *; destruct H_x0_in as [H_x0_in_L|H_x0_in_R].
      right; apply conj.
        assumption.
        destruct (P.t_eq_decidable x1 y) as [H_x1y_eq|H_x1y_neq].
          (* x1 = y *)
          contradict H_x0x1_neq.
            rewrite H_x0_in_L.
            rewrite H_x1y_eq.
            reflexivity.
          (* x1 <> y *)
          left; assumption.
      right; apply conj.
        assumption.
        destruct (P.t_eq_decidable x1 y) as [H_x1y_eq|H_x1y_neq].
          (* x1 = y *)
          destruct (remove_preserves_is_in x0 x1 ys H_x0x1_neq).
            destruct H_x0_in_R as [H_x0_in_RL H_x0_in_RR].
              auto.
          (* x1 <> y *)
          right; apply conj.
            destruct H_x0_in_R as [H_x0_in_RL H_x0_in_RR].
              assumption.
            destruct (remove_preserves_is_in x0 x1 ys H_x0x1_neq).
              destruct H_x0_in_R as [H_x0_in_RL H_x0_in_RR].
                auto.
Qed.

Theorem insert_preserves_is_in_false : forall (x0 x1 : e) (s : t),
  x0 <> x1 -> (~is_in x0 (insert x1 s) <-> ~is_in x0 s).
Proof.
  intros x0 x1 s H_x0x1_neq.
  apply conj.
    intros H_not_in.
    induction s as [|y ys].
      (* s = nil *)
      simpl; auto.
      (* s = y :: ys *)
      simpl in *; destruct (P.t_eq_decidable x1 y) as [H_x1y_eq|H_x1y_neq].
        (* x1 = y *)
        unfold not.
        intros H_contra_goal.
        destruct H_not_in.
          destruct H_contra_goal as [H_cg_L|H_cg_R].
            contradict H_x0x1_neq.
              rewrite H_x1y_eq.
              rewrite H_cg_L.
              reflexivity.
            right; apply conj.
              assumption.
              destruct H_cg_R as [H_cg_RL H_cg_RR].
                destruct (remove_preserves_is_in x0 x1 ys H_x0x1_neq).
                  auto.
        (* x1 <> y *)
        unfold not.
        intros H_contra_goal.
        destruct H_not_in.
          destruct H_contra_goal as [H_cg_L|H_cg_R].
            right; apply conj.
              assumption.
              left; assumption.
            right; apply conj.
              assumption.
              right; apply conj.
                destruct H_cg_R as [H_cg_RL H_cg_RR].
                  auto.
                destruct H_cg_R as [H_cg_RL H_cg_RR].
                  destruct (remove_preserves_is_in x0 x1 ys H_x0x1_neq).
                    auto.

    intros H_not_in.
    induction s as [|y ys].
      (* s = nil *)
      simpl in *.
      unfold not.
      intros H_contra_goal.
      destruct H_contra_goal as [H_cg_L|H_cg_R].
        contradict H_x0x1_neq.
          assumption.
        tauto.
      (* s = y :: ys *)
      simpl in *; destruct (P.t_eq_decidable x1 y) as [H_x1y_eq|H_x1y_neq].
        (* x1 = y *)
        unfold not.
        intros H_contra_goal.
        destruct H_contra_goal as [H_cg_L|H_cg_R].
          contradict H_x0x1_neq.
            assumption.
          destruct H_not_in.
            right; apply conj.
              rewrite <- H_x1y_eq.
              assumption.
              destruct H_cg_R as [H_cg_RL H_cg_RR].
                destruct (remove_preserves_is_in x0 x1 ys H_x0x1_neq).
                  auto.
        (* x1 <> y *)
        unfold not.
        intros H_contra_goal.
        destruct H_not_in.
          simpl in *. destruct H_contra_goal as [H_cg_L|H_cg_R].
            contradict H_x0x1_neq.
              assumption.
            destruct H_cg_R as [H_cg_RL H_cg_RR].
              destruct H_cg_RR as [H_cg_RRL|H_cg_RRR].
                left; assumption.
                right; apply conj.
                  destruct H_cg_RRR as [H_cg_RRRL H_cg_RRRR].
                    assumption.
                  destruct H_cg_RRR as [H_cg_RRRL H_cg_RRRR].
                    destruct (remove_preserves_is_in x0 x1 ys H_x0x1_neq).
                      auto.
Qed.

Theorem singleton_eq : forall (x : e),
  singleton x = insert x empty.
Proof.
  reflexivity.
Qed.

End Make.