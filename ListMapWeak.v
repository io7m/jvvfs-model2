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
Require MapWeak.

Open Scope list_scope.

(** A trivial and extremely inefficient implementation of the [MapWeak]
interface implemented with lists of pairs. *)
Module Make (K : MapWeak.Parameters) : MapWeak.Signature
  with Definition key := K.key.

Definition key := K.key.

Definition t (A : Type) := list (key * A).

Definition empty {A : Type} : t A := nil.

Fixpoint key_in
  {A : Type}
  (k : key)
  (m : t A)
: Prop :=
  match m with
  | nil           => False
  | cons (j, _) m => j = k \/ key_in k m
  end.

Fixpoint key_in_once
  {A : Type}
  (k : key)
  (m : t A)
: Prop :=
  match m with
  | nil           => False
  | cons (j, _) m => (j = k /\ ~key_in k m) \/ (j <> k /\ key_in_once k m)
  end.

Fixpoint key_maps_to
  {A : Type}
  (k : key)
  (x : A)
  (m : t A)
: Prop :=
  match m with
  | nil              => False
  | cons (ke, xe) ys => (ke = k /\ xe = x) \/ (ke <> k /\ key_maps_to k x ys)
  end.

Fixpoint remove
  {A : Type}
  (k : key)
  (m : t A)
: t A :=
  match m with
  | nil             => nil
  | cons (ke, x) ks =>
    match K.key_eq_decidable k ke with
    | left  _ => remove k ks
    | right _ => cons (ke, x) (remove k ks)
    end
  end.

Fixpoint insert
  {A : Type}
  (k : key)
  (x : A)
  (m : t A)
: t A := cons (k, x) (remove k m).

Fixpoint lookup
  {A : Type}
  (k : key)
  (m : t A)
: option A :=
  match m with
  | nil             => None
  | cons (ke, x) ys =>
    match K.key_eq_decidable k ke with
    | left _  => Some x
    | right _ => lookup k ys
    end
  end.

Fixpoint keys
  {A : Type}
  (m : t A)
: list key :=
  match m with
  | nil             => nil
  | cons (ke, x) ys => cons ke (keys ys)
  end.

Fixpoint for_all_values
  {A : Type}
  (P : A -> Prop)
  (m : t A)
: Prop :=
  match m with
  | nil            => True
  | cons (_, x) ys => P x /\ for_all_values P ys
  end.

Fixpoint for_all_keys
  {A : Type}
  (P : key -> Prop)
  (m : t A)
: Prop :=
  match m with
  | nil            => True
  | cons (k, _) ys => P k /\ for_all_keys P ys
  end.

Fixpoint for_all_mappings
  {A : Type}
  (P : key -> A -> Prop)
  (m : t A)
: Prop :=
  match m with
  | nil            => True
  | cons (k, v) ys => P k v /\ for_all_mappings P ys
  end.

Lemma key_in_eq : forall {A : Type} (k : key) (x : A) (m : t A),
  key_in k (cons (k, x) m).
Proof.
  intros A k x m.
  induction m as [|mapping ys].
    simpl; auto.
    simpl; auto.
Qed.

Lemma key_in_cons : forall {A : Type} (k0 k1 : key) (x : A) (m : t A),
  key_in k0 m -> key_in k0 (cons (k1, x) m).
Proof.
  intros A k0 k1 x m H_in.
  induction m as [|mapping ys].
    simpl; auto.
    simpl; auto.
Qed.

Lemma key_in_cons2 : forall {A : Type} (k0 k1 : key) (x : A) (m : t A),
  k0 <> k1 -> key_in k0 (cons (k1, x) m) -> key_in k0 m.
Proof.
  intros A k0 k1 x m H_neq H_in.
  induction m as [|mapping ys].
    contradict H_in.
      simpl; intuition.
    destruct mapping as [ke ve].
      destruct H_in.
        contradict H_neq. symmetry. assumption.
      assumption.
Qed.

Lemma key_in_once_implies_in : forall (A : Type) (k : key) (m : t A),
  key_in_once k m -> key_in k m.
Proof.
  intros A k m H_in.
  induction m as [|y ys].
    (* m = nil *)
    contradict H_in.
    (* m = mapping :: ys *)
    destruct y.
    destruct H_in as [H_in|].
    destruct H_in as [H_eq H_not_in].
    rewrite <- H_eq. apply key_in_eq.

    destruct H.
    assert (key_in k ys) by (apply (IHys H0)).
    apply key_in_cons; assumption.
Qed.

Lemma key_in_once_cons_false : forall (A : Type) (k : key) (v : A) (m : t A),
  key_in_once k m -> ~key_in_once k (cons (k, v) m).
Proof.
  intros A k v m H_once.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; auto.

    (* m = mapping :: ys *)
    simpl; intuition.
    destruct mapping as [mk mv].
    destruct H_once  as [H_once|].
    destruct H_once  as [H_eq H_not_in].
    auto.
    destruct H0.
    assert (key_in k ys) by (apply key_in_once_implies_in; assumption).
    auto.
Qed.

Theorem key_maps_to_in : forall {A : Type} (k : key) (x : A) (m : t A),
  key_maps_to k x m -> key_in k m.
Proof.
  intros A k x m H_maps.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; tauto.
    (* m = mapping :: ys *)
    simpl; destruct mapping as [k_existing v_existing].
      destruct H_maps. tauto.
      right. destruct H. apply (IHys H0).
Qed.

Theorem key_in_false_maps_to_any : forall {A : Type} (k : key) (x : A) (m : t A),
  ~key_in k m -> ~key_maps_to k x m.
Proof.
  intros A k x m H_not_in.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; auto.
    (* m = mapping :: ys *)
    simpl; destruct mapping as [ke ve].
      simpl in *.
      intuition.
Qed.

Lemma key_in_cons_false : forall {A : Type} (k0 k1 : key) (x : A) (m : t A),
  k0 <> k1 -> ~key_in k0 (cons (k1, x) m) -> ~key_in k0 m.
Proof.
  intros A k0 k1 x m H_neq H_not_in.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; auto.
    (* m = mapping :: ys *)
    destruct mapping as [ke ve].
      unfold not. intro H_in. simpl in *.
      destruct H_not_in.
      destruct H_in.
      right. left. assumption.
      right. right. assumption.
Qed.

Lemma key_maps_to_cons1 : forall {A : Type} (k0 k1 : key) (x0 x1 : A) (m : t A),
  k0 <> k1 -> key_maps_to k0 x0 (cons (k1, x1) m) -> key_maps_to k0 x0 m.
Proof.
  intros A k0 k1 x0 x1 m H_neq H_maps.
  induction m as [|mapping ys].
    (* m = nil *)
    contradict H_maps. simpl. intuition.
    (* m = mapping :: ys *)
    destruct mapping as [k_existing v_existing].
      destruct H_maps.
      simpl. intuition.
      right.
      split.
      intuition.
      apply IHys. simpl. auto.
      destruct H.
      assumption.
Qed.

Lemma key_maps_to_cons2 : forall {A : Type} (k0 k1 : key) (x0 x1 : A) (m : t A),
  k0 <> k1 -> key_maps_to k0 x0 m -> key_maps_to k0 x0 (cons (k1, x1) m).
Proof.
  intros A k0 k1 x0 x1 m H_neq H_maps.
  induction m as [|mapping ys].
    (* m = nil *)
    contradict H_maps.
    (* m = mapping :: ys *)
    destruct mapping as [ke ve]; simpl; auto.
Qed.

Theorem key_maps_to_eq_value : forall {A : Type} (k0 k1 : key) (x0 x1 : A) (m : t A),
  k0 = k1 -> key_maps_to k0 x0 m -> key_maps_to k1 x1 m -> x0 = x1.
Proof.
  intros A k0 k1 x0 x1 m H_keq H_k0maps H_k1maps.
  induction m as [|mapping ys].
    (* m = nil *)
    inversion H_k0maps.
    (* m = mapping :: ys *)
    destruct mapping as [ke ve].
    simpl in *.
    destruct H_k0maps as [H_k0L|H_k0R].
      destruct H_k0L as [H_k0L_keq H_k0L_veq].
        destruct H_k1maps as [H_k1L|H_k1R].
          destruct H_k1L as [H_k1L_keq H_k1L_veq].
            rewrite <- H_k0L_veq.
            rewrite <- H_k1L_veq.
            reflexivity.
          destruct H_k1R as [H_k1R_neq H_k1R_maps].
            contradict H_keq.
              rewrite <- H_k0L_keq.
              assumption.
      destruct H_k0R as [H_k0R_neq H_k0R_maps].
        destruct H_k1maps as [H_k1L|H_k1R].
          destruct H_k1L as [H_k1L_keq H_k1L_veq].
            contradict H_keq.
              apply not_eq_sym.
              rewrite <- H_k1L_keq.
              assumption.
          destruct H_k1R as [H_k1R_neq H_k1R_maps].
            apply IHys.
              assumption.
              assumption.
Qed.

Theorem key_maps_to_neq_keys : forall {A : Type} (k0 k1 : key) (x0 x1 : A) (m : t A),
  x0 <> x1 -> key_maps_to k0 x0 m -> key_maps_to k1 x1 m -> k0 <> k1.
Proof.
  intros A k0 k1 x0 x1 m H_keq H_k0maps H_k1maps.
  induction m as [|mapping ys].
    (* m = nil *)
    inversion H_k0maps.
    (* m = mapping :: ys *)
    destruct mapping as [ke ve].
    simpl in *.
    destruct H_k0maps as [H_k0L|H_k0R].
      destruct H_k0L as [H_k0L_keq H_k0L_veq].
        destruct H_k1maps as [H_k1L|H_k1R].
          destruct H_k1L as [H_k1L_keq H_k1L_veq].
            contradict H_keq.
              rewrite <- H_k0L_veq.
              rewrite <- H_k1L_veq.
              reflexivity.
          destruct H_k1R as [H_k1R_neq H_k1R_maps].
            rewrite <- H_k0L_keq.
            assumption.
      destruct H_k0R as [H_k0R_neq H_k0R_maps].
        destruct H_k1maps as [H_k1L|H_k1R].
          destruct H_k1L as [H_k1L_keq H_k1L_veq].
            rewrite <- H_k1L_keq.
            apply not_eq_sym.
            assumption.
          destruct H_k1R as [H_k1R_neq H_k1R_maps].
            auto.
Qed.

Theorem empty_in_false : forall {A : Type} (k : key),
  ~key_in k (@empty A).
Proof. auto. Qed.

Theorem empty_maps_to_false : forall {A : Type} (k : key) (x : A),
  ~key_maps_to k x (@empty A).
Proof. auto. Qed.

Theorem remove_not_maps_to : forall {A : Type} (k : key) (x : A) (m : t A),
  ~key_maps_to k x (remove k m).
Proof.
  intros A k x m.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; auto.
    (* m = mapping :: ys *)
    destruct mapping as [ke xe].
      simpl; destruct (K.key_eq_decidable k ke).
        assumption.
        simpl; intuition.
Qed.

Theorem remove_not_in : forall {A : Type} (k : key) (m : t A),
  ~key_in k (remove k m).
Proof.
  intros A k m.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; auto.
    (* m = mapping :: ys *)
    destruct mapping as [ke xe].
      simpl; destruct (K.key_eq_decidable k ke) as [H_keq|H_kneq].
        (* k = ke *)
        assumption.
        (* k <> ke *)
        simpl; intuition.
Qed.

Theorem remove_preserves_maps_to : forall {A : Type} (k0 k1 : key) (x : A) (m : t A),
  k0 <> k1 -> key_maps_to k0 x m -> key_maps_to k0 x (remove k1 m).
Proof.
  intros A k0 k1 x m H_neq H_maps.
  induction m as [|mapping ys].
    (* m = nil *)
    inversion H_maps.
    (* m = mapping :: ys *)
    destruct mapping as [ke xe].
      simpl; destruct (K.key_eq_decidable k1 ke) as [H_keq|H_kneq].
        (* k1 = ke *)
        apply IHys.
        apply (key_maps_to_cons1 k0 ke x xe ys).
        rewrite H_keq in H_neq.
        assumption.
        assumption.
        (* k1 <> ke *)
        inversion H_maps.
          simpl; left; assumption.
          simpl; right; intuition.
Qed.

Theorem remove_preserves_maps_to_alt : forall {A : Type} (k0 k1 : key) (x : A) (m : t A),
  k0 <> k1 -> key_maps_to k0 x (remove k1 m) -> key_maps_to k0 x m.
Proof.
  intros A k0 k1 x m H_neq H_maps.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; auto.
    (* m = mapping :: ys *)
    destruct mapping as [ke xe].
    destruct (K.key_eq_decidable k0 ke) as [H_k0ke_eq|H_k0ke_neq].
      (* k0 = ke *)
      simpl in *; destruct (K.key_eq_decidable k1 ke) as [H_k1ke_eq|H_k1ke_neq].
        (* k1 = ke *)
        contradict H_k0ke_eq; rewrite <- H_k1ke_eq; assumption.
        (* k1 <> ke *)
        simpl in *.
        destruct H_maps as [H_maps_L|H_maps_R].
          left; assumption.
          right; apply conj.
            destruct H_maps_R as [H_maps_RL H_maps_RR].
              assumption.
            apply IHys.
            destruct H_maps_R as [H_maps_RL H_maps_RR].
              assumption.
      (* k0 <> ke *)
      simpl in *; destruct (K.key_eq_decidable k1 ke) as [H_k1ke_eq|H_k1ke_neq].
        (* k1 = ke *)
        right; apply conj.
          auto.
          apply IHys; assumption.
        (* k1 <> ke *)
        simpl in *.
        destruct H_maps as [H_maps_L|H_maps_R].
          left. assumption.
          right; apply conj.
            auto.
            destruct H_maps_R as [H_maps_RL H_maps_RR].
              apply IHys. assumption.
Qed.

Theorem remove_preserves_not_maps_to_alt : forall {A : Type} (k0 k1 : key) (x : A) (m : t A),
  k0 <> k1 -> ~key_maps_to k0 x (remove k1 m) -> ~key_maps_to k0 x m.
Proof.
  intros A k0 k1 x m H_neq H_not_maps.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; auto.
    (* m = mapping :: ys *)
    destruct mapping as [ke xe].
    destruct (K.key_eq_decidable k0 ke) as [H_k0ke_eq|H_k0ke_neq].
      (* k0 = ke *)
      simpl in *; destruct (K.key_eq_decidable k1 ke) as [H_k1ke_eq|H_k1ke_neq].
        (* k1 = ke *)
        contradict H_neq.
          rewrite H_k1ke_eq.
          rewrite H_k0ke_eq.
          reflexivity.
        (* k1 <> ke *)
        unfold not.
        intros H_contra_goal.
        unfold not in H_not_maps.
        destruct H_not_maps.
        simpl in *.
        destruct H_contra_goal as [H_cg_L|H_cg_R].
          left; assumption.
          right; apply conj.
            destruct H_cg_R as [H_cg_RL H_cg_RR].
              destruct (H_cg_RL (eq_sym H_k0ke_eq)).
            destruct H_cg_R as [H_cg_RL H_cg_RR].
              destruct (H_cg_RL (eq_sym H_k0ke_eq)).
      (* k0 <> ke *)
      simpl in *; destruct (K.key_eq_decidable k1 ke) as [H_k1ke_eq|H_k1ke_neq].
        (* k1 = ke *)
        unfold not.
        intros H_contra_goal.
        unfold not in H_not_maps.
        destruct H_not_maps.
        destruct H_contra_goal as [H_cg_L|H_cg_R].
          destruct H_cg_L as [H_cg_LL H_cg_LR].
            contradict H_k0ke_neq.
              symmetry.
              assumption.
          destruct H_cg_R as [H_cg_RL H_cg_RR].
            apply (remove_preserves_maps_to k0 k1 x ys H_neq H_cg_RR).
        (* k1 <> ke *)
        unfold not.
        intros H_contra_goal.
        unfold not in H_not_maps.
        destruct H_not_maps.
        simpl in *.
        destruct H_contra_goal as [H_cg_L|H_cg_R].
          left; assumption.
          right; apply conj.
            destruct H_cg_R as [H_cg_RL H_cg_RR].
              assumption.
            destruct H_cg_R as [H_cg_RL H_cg_RR].
              apply (remove_preserves_maps_to k0 k1 x ys H_neq H_cg_RR).
Qed.

Theorem remove_preserves_not_in : forall {A : Type} (k0 k1 : key) (m : t A),
  ~key_in k0 m -> ~key_in k0 (remove k1 m).
Proof.
  intros A k0 k1 m H_not_in.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; auto.
    (* m = mapping :: ys *)
    destruct mapping as [ke xe].
    simpl in *.
    destruct (K.key_eq_decidable k1 ke) as [H_keq|H_kneq].
      (* k1 = ke *)
      assert (~key_in k0 ys) by auto.
      apply IHys. assumption.
      (* k1 <> ke *)
      simpl. intuition.
Qed.

Theorem remove_preserves_in : forall {A : Type} (k0 k1 : key) (m : t A),
  k0 <> k1 -> key_in k0 m -> key_in k0 (remove k1 m).
Proof.
  intros A k0 k1 m H_neq H_in.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; auto.
    (* m = mapping :: ys *)
    destruct mapping as [ke xe].
    simpl; destruct (K.key_eq_decidable k1 ke) as [H_keq|H_kneq].
      (* k1 = ke *)
      apply IHys.
      rewrite <- H_keq in H_in.
      apply (key_in_cons2 k0 k1 xe ys H_neq H_in).
      (* k1 <> ke *)
      destruct H_in.
        rewrite H.
        simpl. left. reflexivity.
        simpl. right. apply IHys. assumption.
Qed.

Theorem remove_preserves_not_in_alt : forall {A : Type} (k0 k1 : key) (m : t A),
  k0 <> k1 -> ~key_in k0 (remove k1 m) -> ~key_in k0 m.
Proof.
  intros A k0 k1 m H_neq H_not_in.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; auto.
    (* m = mapping :: ys *)
    destruct mapping as [ke xe].
    destruct (K.key_eq_decidable k0 ke) as [H_k0ke_eq|H_k0ke_neq].
      (* k0 = ke *)
      simpl in *; destruct (K.key_eq_decidable k1 ke) as [H_k1ke_eq|H_k1ke_neq].
        (* k1 = ke *)
        contradict H_neq.
        rewrite H_k1ke_eq.
        rewrite H_k0ke_eq.
        reflexivity.
        (* k1 <> ke *)
        unfold not.
        intros H_contra_goal.
        unfold not in H_not_in.
        destruct H_not_in.
        simpl in *.
        destruct H_contra_goal as [H_cg_L|H_cg_R].
          left; assumption.
          right; apply (remove_preserves_in k0 k1 ys H_neq H_cg_R).
      (* k0 <> ke *)
      simpl in *; destruct (K.key_eq_decidable k1 ke) as [H_k1ke_eq|H_k1ke_neq].
        (* k1 = ke *)
        unfold not.
        intros H_contra_goal.
        unfold not in H_not_in.
        destruct H_not_in.
        destruct H_contra_goal as [H_cg_L|H_cg_R].
          contradict H_k0ke_neq; auto.
          apply (remove_preserves_in k0 k1 ys H_neq H_cg_R).
        (* k1 <> ke *)
        unfold not.
        intros H_contra_goal.
        unfold not in H_not_in.
        destruct H_not_in.
        simpl in *.
        destruct H_contra_goal as [H_cg_L|H_cg_R].
          left; assumption.
          right; apply (remove_preserves_in k0 k1 ys H_neq H_cg_R).
Qed.

Theorem remove_preserves_in_alt : forall {A : Type} (k0 k1 : key) (m : t A),
  k0 <> k1 -> key_in k0 (remove k1 m) -> key_in k0 m.
Proof.
  intros A k0 k1 m H_neq H_in.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; auto.
    (* m = mapping :: ys *)
    destruct mapping as [ke xe].
    simpl; destruct (K.key_eq_decidable k1 ke) as [H_keq|H_kneq].
      (* k1 = ke *)
      right. apply IHys.
      rewrite <- H_keq in H_in.
      simpl in H_in.
      destruct (K.key_eq_decidable k1 k1) as [H_k1k1_eq|H_k1k1_neq].
        assumption.
        contradict H_k1k1_neq. reflexivity.
      (* k1 <> ke *)
      simpl in *.
      destruct (K.key_eq_decidable k1 ke) as [H_k1ke_eq|H_k1ke_neq].
        contradict H_k1ke_eq. assumption.
        simpl in *.
        destruct H_in.
          left; assumption.
          right; apply IHys; assumption.
Qed.

Theorem remove_preserves_not_maps_to : forall {A : Type} (k0 k1 : key) (x : A) (m : t A),
  ~key_maps_to k0 x m -> ~key_maps_to k0 x (remove k1 m).
Proof.
  intros A k0 k1 x m H_not_maps.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; auto.
    (* m = mapping :: ys *)
    destruct mapping as [ke xe].
    destruct (K.key_eq_decidable k0 ke) as [H_k0ke_eq|H_k0ke_neq].
      (* k0 = ke *)
      simpl in *; destruct (K.key_eq_decidable k1 ke) as [H_k1ke_eq|H_k1ke_neq].
        (* k1 = ke *)
        rewrite H_k0ke_eq.
        rewrite H_k1ke_eq.
        apply remove_not_maps_to.
        (* k1 <> ke *)
        unfold not.
        intros H_contra_goal.
        unfold not in H_not_maps.
        destruct H_not_maps.
        simpl in *.
        destruct H_contra_goal as [H_cg_L|H_cg_R].
          left; assumption.
          right. destruct H_cg_R as [H_cg_RL H_cg_RR].
            apply conj.
              assumption.
              apply (remove_preserves_maps_to_alt k0 k1 x ys).
                rewrite <- H_k0ke_eq in H_k1ke_neq.
                apply not_eq_sym.
                assumption.
              assumption.
      (* k0 <> ke *)
      simpl in *; destruct (K.key_eq_decidable k1 ke) as [H_k1ke_eq|H_k1ke_neq].
        (* k1 = ke *)
        unfold not.
        intros H_contra_goal.
        unfold not in H_not_maps.
        destruct H_not_maps.
        right. apply conj.
          apply not_eq_sym in H_k0ke_neq.
            assumption.
          apply (remove_preserves_maps_to_alt k0 k1 x ys).
            rewrite H_k1ke_eq.
            assumption.
            assumption.
        (* k1 <> ke *)
        unfold not.
        intros H_contra_goal.
        unfold not in H_not_maps.
        destruct H_not_maps.
        simpl in *.
        destruct H_contra_goal as [H_cg_L|H_cg_R].
          left; assumption.
          right; apply conj.
            apply not_eq_sym in H_k0ke_neq.
              assumption.
            destruct H_cg_R as [H_cg_RL H_cg_RR].
              destruct (K.key_eq_decidable k0 k1) as [H_k0k1_eq|H_k0k1_neq].
                contradict H_cg_RR.
                  rewrite H_k0k1_eq.
                  apply (remove_not_maps_to k1 x ys).
                apply (remove_preserves_maps_to_alt k0 k1 x ys H_k0k1_neq H_cg_RR).
Qed.

Theorem insert_maps_to : forall {A : Type} (k : key) (x : A) (m : t A),
  key_maps_to k x (insert k x m).
Proof.
  intros A k x m.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; auto.
    (* m = mapping :: ys *)
    destruct mapping as [ke xe].
      simpl; destruct (K.key_eq_decidable k ke) as [H_keq|H_kneq]; auto.
Qed.

Theorem insert_preserves_maps_to : forall {A : Type} (k0 k1 : key) (x0 x1 : A) (m : t A),
  k0 <> k1 -> key_maps_to k0 x0 m -> key_maps_to k0 x0 (insert k1 x1 m).
Proof.
  intros A k0 k1 x0 x1 m H_neq H_maps.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; auto.
    (* m = mapping :: ys *)
    destruct mapping as [ke xe].
      simpl; destruct (K.key_eq_decidable k1 ke) as [H_keq|H_kneq].
        (* k1 = ke *)
        rewrite <- H_keq in H_maps.
        right. split.
          apply not_eq_sym; auto.
          apply remove_preserves_maps_to.
            assumption.
            apply (key_maps_to_cons1 k0 k1 x0 xe ys H_neq H_maps).
        (* k1 <> ke *)
        right. split.
          apply not_eq_sym; auto.
          simpl; destruct H_maps.
            left; assumption.
            destruct H as [HL HR].
              right.
                split. assumption.
                apply remove_preserves_maps_to.
                  assumption.
                  assumption.
Qed.

Theorem insert_preserves_not_in : forall {A : Type} (k0 k1 : key) (x : A) (m : t A),
  k0 <> k1 -> ~key_in k0 m -> ~key_in k0 (insert k1 x m).
Proof.
  intros A k0 k1 x m H_neq H_not_in.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; intuition.
    (* m = mapping :: ys *)
    destruct mapping as [ke xe].
    simpl; destruct (K.key_eq_decidable k1 ke) as [H_keq|H_kneq].
      unfold not. intros H_contra.
      destruct H_contra as [H_contra_L|H_contra_R].
        contradict H_contra_L.
          apply not_eq_sym.
          assumption.
        contradict H_contra_R.
          rewrite H_keq in H_neq.
          assert (~key_in k0 ys) as H_not_in_ys.
            apply (key_in_cons_false k0 ke xe ys H_neq H_not_in).
          apply (remove_preserves_not_in k0 k1 ys H_not_in_ys).
      simpl in *.
      unfold not. intros H_contra.
      destruct H_contra as [H_contra_L|H_contra_R].
        contradict H_contra_L.
          apply not_eq_sym.
          assumption.
        destruct H_contra_R as [H_cR_L|H_cR_R].
          contradict H_not_in.
            left. assumption.
          contradict H_not_in.
            right. apply (remove_preserves_in_alt k0 k1 ys H_neq H_cR_R).
Qed.

Theorem insert_preserves_not_maps_to : forall {A : Type} (k0 k1 : key) (x0 x1 : A) (m : t A),
  k0 <> k1 -> ~key_maps_to k0 x0 m -> ~key_maps_to k0 x0 (insert k1 x1 m).
Proof.
  intros A k0 k1 x0 x1 m H_kneq H_nmaps.
  induction m as [|mapping ys].
    (* m = nil *)
    simpl; intuition.
    (* m = mapping :: ys *)
    destruct mapping as [ke xe].
    unfold not.
    intros H_contra_goal.
    unfold not in H_nmaps.
    destruct H_nmaps.
    destruct (K.key_eq_decidable k0 ke) as [H_k0ke_eq|H_k0ke_neq].
      (* k0 = ke *)
      simpl in *; destruct (K.key_eq_decidable k1 ke) as [H_k1ke_eq|H_k1ke_neq].
        (* k1 = ke *)
        contradict H_kneq.
          rewrite H_k1ke_eq.
          rewrite H_k0ke_eq.
          reflexivity.
        (* k1 <> ke *)
        destruct H_contra_goal as [H_cg_L|H_cg_R].
          contradict H_k1ke_neq.
            destruct H_cg_L as [H_cg_LL H_cg_LR].
              rewrite H_cg_LL.
              rewrite H_k0ke_eq.
              reflexivity.
          simpl in *.
          destruct H_cg_R as [H_cg_RL H_cg_RR].
            destruct H_cg_RR as [H_cg_RRL|H_cg_RRR].
              left; assumption.
              right; apply conj.
                destruct H_cg_RRR as [H_cg_RRRL H_cg_RRRR].
                  assumption.
                destruct H_cg_RRR as [H_cg_RRRL H_cg_RRRR].
                  apply (remove_preserves_maps_to_alt k0 k1 x0 ys H_kneq H_cg_RRRR).
      (* k0 <> ke *)
      simpl in *; destruct (K.key_eq_decidable k1 ke) as [H_k1ke_eq|H_k1ke_neq].
        (* k1 = ke *)
        destruct H_contra_goal as [H_cg_L|H_cg_R].
          contradict H_k1ke_eq.
            destruct H_cg_L.
              auto.
          right. rewrite <- H_k1ke_eq.
            destruct H_cg_R as [H_cg_RL H_cg_RR].
              apply conj.
                assumption.
                apply (remove_preserves_maps_to_alt k0 k1 x0 ys H_kneq H_cg_RR).
        (* k1 <> ke *)
        simpl in *.
        destruct H_contra_goal as [H_cg_L|H_cg_R].
          destruct H_cg_L as [H_cg_LL H_cg_LR].
            contradict H_kneq.
              auto.
          destruct H_cg_R as [H_cg_RL H_cg_RR].
            destruct H_cg_RR as [H_cg_RRL|H_cg_RRR].
              left; assumption.
              right; apply conj.
                apply not_eq_sym; assumption.
                destruct H_cg_RRR as [H_cg_RRRL H_cg_RRRR].
                  apply (remove_preserves_maps_to_alt k0 k1 x0 ys H_kneq H_cg_RRRR).
Qed.

Lemma lookup_maps_to_some_support : forall {A : Type} (k : key) (x : A) (m : t A),
  key_maps_to k x m -> lookup k m = Some x.
Proof.
  intros A k x m H_maps.
  induction m as [|mapping ys].
    (* m = nil *)
    inversion H_maps.
    (* m = mapping :: ys *)
    destruct mapping as [ke xe].
      simpl; destruct (K.key_eq_decidable k ke) as [H_keq|H_kneq].
        destruct H_maps as [H_mL|H_mR].
          destruct H_mL as [H_mL_L H_mL_R].
            rewrite H_mL_R.
            reflexivity.
          destruct H_mR as [H_mR_L H_mR_R].
            contradict H_mR_L; auto.
        destruct H_maps as [H_mL|H_mR].
          destruct H_mL as [H_mL_L H_mL_R].
            contradict H_mL_L; auto.
          destruct H_mR as [H_mR_L H_mR_R].
            apply IHys.
            assumption.
Qed.

Lemma lookup_some_maps_to_support : forall {A : Type} (k : key) (x : A) (m : t A),
  lookup k m = Some x -> key_maps_to k x m.
Proof.
  intros A k x m H_lookup.
  induction m as [|mapping ys].
    (* m = nil *)
    inversion H_lookup.
    (* m = mapping :: ys *)
    destruct mapping as [ke xe].
    simpl in *.
    destruct (K.key_eq_decidable k ke) as [H_keq|H_kneq] in H_lookup.
      left; apply conj.
        auto.
        inversion H_lookup; reflexivity.
      right; apply conj.
        apply not_eq_sym; assumption.
        apply IHys; assumption.
Qed.

Theorem lookup_maps_to_some : forall {A : Type} (k : key) (x : A) (m : t A),
  key_maps_to k x m <-> lookup k m = Some x.
Proof.
  intros A k x m.
  apply conj.
    apply lookup_maps_to_some_support.
    apply lookup_some_maps_to_support.
Qed.

Lemma lookup_cons_none : forall {A : Type} (k0 k1 : key) (x : A) (m : t A),
  lookup k0 (cons (k1, x) m) = None -> lookup k0 m = None.
Proof.
  intros A k0 k1 x m H_none.
  simpl in *.
    destruct (K.key_eq_decidable k0 k1) as [H_keq|H_kneq].
      inversion H_none.
      assumption.
Qed.

Theorem lookup_not_in_none : forall {A : Type} (k : key) (m : t A),
  ~key_in k m <-> lookup k m = None.
Proof.
  intros A k m.
  apply conj.
    intros H_in.
    induction m as [|mapping ys].
      (* m = nil *)
      reflexivity.
      (* m = mapping :: ys *)
      destruct mapping as [ke xe].
      simpl; destruct (K.key_eq_decidable k ke) as [H_keq|H_kneq].
        (* k = ke *)
        rewrite H_keq in H_in.
        contradict H_in.
          simpl; left; reflexivity.
        (* k <> ke *)
        apply IHys.
        apply (key_in_cons_false k ke xe ys H_kneq H_in).
    intros H_in.
    induction m as [|mapping ys].
      (* m = nil *)
      auto.
      (* m = mapping :: ys *)
      destruct mapping as [ke xe].
      simpl; destruct (K.key_eq_decidable k ke) as [H_keq|H_kneq].
        (* k = ke *)
        rewrite H_keq in H_in.
        contradict H_in.
          simpl; destruct (K.key_eq_decidable ke ke) as [H_keke_eq|H_keke_neq].
            discriminate.
            contradict H_keke_neq.
              reflexivity.
        (* k <> ke *)
        simpl.
        unfold not.
        intros H_conj.
        destruct H_conj.
          contradict H_kneq. symmetry. assumption.
          contradict H. apply IHys. apply (lookup_cons_none k ke xe ys H_in).
Qed.

Theorem keys_in : forall {A : Type} (m : t A) (k : key),
  key_in k m = List.In k (keys m).
Proof.
  intros A m k.
  induction m as [|mapping ys].
    reflexivity.
    destruct mapping as [ke xe].
      simpl; rewrite IHys; reflexivity.
Qed.

Theorem keys_in_false : forall {A : Type} (m : t A) (k : key),
  (~key_in k m) = (~List.In k (keys m)).
Proof.
  intros A m k.
  rewrite keys_in.
  reflexivity.
Qed.

Lemma pair_eq_iff : forall (A B : Type) (x0 x1 : A) (y0 y1 : B),
  (x0, y0) = (x1, y1) <-> x0 = x1 /\ y0 = y1.
Proof.
  intros A B x0 x1 y0 y1.
  apply conj.
    intros H_eq.
    apply conj.
      injection H_eq; auto.
      injection H_eq; auto.
    intros H_eq.
    destruct H_eq as [H_xeq H_yeq].
      rewrite H_xeq.
      rewrite H_yeq.
      reflexivity.
Qed.

Theorem keys_empty : forall {A : Type} (m : t A),
  keys m = nil <-> m = empty.
Proof.
  induction m as [|mh mr].
    split; auto.
    split.
      intros Hk.
      contradict Hk.
        assert (forall k, k :: keys mr <> nil) by discriminate.
        simpl.
        assert ((let (ke, _) := mh in ke :: keys mr) = (fst mh) :: keys mr) as H0.
          destruct mh; reflexivity.
        rewrite H0.
        apply (H (fst mh)).
      intros Hk.
        inversion Hk.
Qed.

Theorem empty_decidable : forall {A : Type} (m : t A),
  {m = empty}+{~m = empty}.
Proof.
  destruct m.
    left; auto.
    right; discriminate.
Qed.

Theorem key_maps_to_not : forall
  {A   : Type}
  (k   : key)
  (x y : A)
  (m   : t A),
  x <> y -> key_maps_to k x m -> ~key_maps_to k y m.
Proof.
  intros A k x y m H_neq H_maps.
  induction m as [|mapping rest].
    inversion H_maps.
    destruct mapping as [mapping_k mapping_v].
      simpl in *.
      intro H_contra.
      intuition.
      assert (x = y) as H_xy.
        rewrite <- H3.
        rewrite <- H1.
        reflexivity.
      apply (H_neq H_xy).
Qed.         

Theorem key_maps_to_decidable : forall
  {A : Type}
  (k : key)
  (x : A)
  (m : t A)
  (e : forall (x y : A), {x = y}+{~x = y}),
  {key_maps_to k x m}+{~key_maps_to k x m}.
Proof.
  intros A k x m e.
  remember (lookup k m) as H_look.
  destruct (H_look).
    symmetry in HeqH_look.
    destruct (e a x) as [H_ax|H_nax].
      rewrite H_ax in HeqH_look.
      destruct (lookup_maps_to_some k x m) as [H0 H1].
        pose proof (H1 HeqH_look) as H_maps.
        left; assumption.
      destruct (lookup_maps_to_some k a m) as [H0 H1].
        pose proof (H1 HeqH_look) as H_maps.
        pose proof (key_maps_to_not k a x m H_nax H_maps) as H_not.
        right; assumption.
    symmetry in HeqH_look.
    destruct (lookup_not_in_none k m) as [H_noneL H_noneR].
      pose proof (H_noneR HeqH_look) as H_none.
      right. apply (key_in_false_maps_to_any k x m H_none).
Qed.

Theorem for_all_values_empty : forall
  {A : Type}
  (P : A -> Prop),
  for_all_values P empty.
Proof.
  intros; exact I.
Qed.

Theorem for_all_keys_empty : forall
  {A : Type}
  (P : key -> Prop),
  for_all_keys P (@empty A).
Proof.
  intros; exact I.
Qed.

Theorem for_all_values_remove : forall
  {A : Type}
  (P : A -> Prop)
  (m : t A)
  (k : key)
  (x : A),
  for_all_values P m -> for_all_values P (remove k m).
Proof.
  induction m as [|mapping rest].
    simpl; auto.
    intros.
    simpl; destruct mapping as [mk mv].
      destruct (K.key_eq_decidable k mk) as [H_keq|H_kneq].
        destruct H as [HL HR].
        apply (IHrest k x HR).
        destruct H as [HL HR].
        simpl; auto.
Qed.

Theorem for_all_values_insert : forall
  {A : Type}
  (P : A -> Prop)
  (m : t A)
  (k : key)
  (x : A),
  P x -> for_all_values P m -> for_all_values P (insert k x m).
Proof.
  intros A P.
  induction m as [|mapping rest].
    simpl; auto.
    intros.
    simpl; destruct mapping as [mk mv].
      destruct (K.key_eq_decidable k mk) as [H_keq|H_kneq].
        destruct H0 as [HL HR].
        split.
          assumption.
          apply (for_all_values_remove P rest k x HR).
        destruct H0 as [HL HR].
        split.
          assumption.
          split.
            assumption.
            apply (for_all_values_remove P rest k x HR).
Qed.

Theorem for_all_values_maps : forall
  {A : Type}
  (P : A -> Prop)
  (m : t A)
  (k : key)
  (x : A),
  for_all_values P m -> key_maps_to k x m -> P x.
Proof.
  intros A P.
  induction m as [|mapping rest].
    intros. inversion H0.
    intros.
    simpl; destruct mapping as [mk mv].
      destruct H0  as [H0L|H0R].
      destruct H0L as [H0LL H0LR].
      destruct H   as [HL HR].
      destruct (K.key_eq_decidable k mk) as [H_keq|H_kneq].
        rewrite <- H0LR.
        assumption.
        rewrite <- H0LR.
        assumption.
      destruct H   as [HL HR].
      destruct H0R as [H0RL H0RR].
      apply (IHrest k x HR H0RR).
Qed.

Theorem for_all_mappings_empty : forall
  {A : Type}
  (P : key -> A -> Prop),
  for_all_mappings P empty.
Proof.
  intros; exact I.
Qed.

Theorem for_all_mappings_remove : forall
  {A : Type}
  (P : key -> A -> Prop)
  (m : t A)
  (k : key),
  for_all_mappings P m -> for_all_mappings P (remove k m).
Proof.
  induction m as [|mapping rest].
    simpl; auto.
    intros.
    simpl; destruct mapping as [mk mv].
      destruct (K.key_eq_decidable k mk) as [H_keq|H_kneq].
        destruct H as [HL HR].
        apply (IHrest k HR).
        destruct H as [HL HR].
        simpl; auto.
Qed.

Theorem for_all_mappings_insert : forall
  {A : Type}
  (P : key -> A -> Prop)
  (m : t A)
  (k : key)
  (x : A),
  P k x -> for_all_mappings P m -> for_all_mappings P (insert k x m).
Proof.
  intros A P.
  induction m as [|mapping rest].
    simpl; auto.
    intros.
    simpl; destruct mapping as [mk mv].
      destruct (K.key_eq_decidable k mk) as [H_keq|H_kneq].
        destruct H0 as [HL HR].
        split.
          assumption.
          apply (for_all_mappings_remove P rest k HR).
        destruct H0 as [HL HR].
        split.
          assumption.
          split.
            assumption.
            apply (for_all_mappings_remove P rest k HR).
Qed.

Theorem for_all_mappings_maps : forall
  {A : Type}
  (P : key -> A -> Prop)
  (m : t A)
  (k : key)
  (x : A),
  for_all_mappings P m -> key_maps_to k x m -> P k x.
Proof.
  intros A P.
  induction m as [|mapping rest].
    intros. inversion H0.
    intros.
    simpl; destruct mapping as [mk mv].
      destruct H0  as [H0L|H0R].
      destruct H0L as [H0LL H0LR].
      destruct H   as [HL HR].
      destruct (K.key_eq_decidable k mk) as [H_keq|H_kneq].
        rewrite <- H0LL.
        rewrite <- H0LR.
        assumption.
        rewrite <- H0LL.
        rewrite <- H0LR.
        assumption.
      destruct H   as [HL HR].
      destruct H0R as [H0RL H0RR].
      apply (IHrest k x HR H0RR).
Qed.

End Make.
