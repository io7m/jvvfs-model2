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
(** The error monad. *)

Require Coq.Lists.List.
Require ListAux.

Open Scope list_scope.

(** A computation that returns a value of type [F] on
    failure, or a value of type [S] on success. *)
Inductive t (F S : Type) : Type :=
  | Success : S -> t F S
  | Failure : F -> t F S.

Arguments Success [F S] _.
Arguments Failure [F S] _.

(** Run the computation [m] and pass the result to [f], returning
    a new computation. *)
Definition bind
  {F S T : Type}
  (m     : t F S)
  (f     : S -> t F T)
: t F T :=
  match m with
  | Success x => f x
  | Failure e => Failure e
  end.

Module Notations.
  Notation "m >>= f" := (bind m f)            (at level 50, left associativity) : error_monad_scope.
  Notation "m >>  f" := (bind m (fun _ => f)) (at level 50, left associativity) : error_monad_scope.
End Notations.

Import Notations.

(** Return a computation that returns the value [x]. *)
Definition return_m
  {F S : Type}
  (x   : S)
: t F S := Success x.

Open Scope error_monad_scope.

(** The left identity law trivially holds. *)
Theorem left_identity : forall (F S T : Type) (f : S -> t F T) (x : S),
  return_m x >>= f = f x.
Proof.
  reflexivity.
Qed.

(** The right identity law trivially holds by induction on [m]. *)
Theorem right_identity : forall (F S T : Type) (m : t F S),
  m >>= return_m = m.
Proof.
  intros F S T m.
  induction m; reflexivity.
Qed.

(** The associativity law trivially holds by induction on [m]. *)
Theorem associativity : forall (F S T U : Type) (m : t F S) (f : S -> t F T) (g : T -> t F U),
  (m >>= f) >>= g = m >>= (fun x => f x >>= g).
Proof.
  intros F S T U m f g.
  induction m; reflexivity.
Qed.

(** If [f >>= g] is successful, then all of the computations must have been successful. *)
Theorem bind_inversion : forall (F S T : Type) (f : t F S) (g : S -> t F T) (x : T),
  f >>= g = Success x -> 
    exists y, f = Success y /\ g y = Success x.
Proof.
  intros until x.
  destruct f; simpl; intros.
  exists s; auto.
  discriminate.
Qed.

(** If [f >>= g] fails, then one of the computations must have failed. *)
Theorem bind_inversion_failure : forall (F S T : Type) (f : t F S) (g : S -> t F T) (e : F),
  f >>= g = Failure e -> 
    (f = Failure e \/ exists s, g s = Failure e).
Proof.
  intros until e.
  destruct f; simpl; intros.
  right. exists s. assumption.
  left.
    injection H.
    intros He.
    rewrite He.
    reflexivity.
Qed.

(** Apply [f] to each element of [ts], accumulating the results,
    using [x] as the initial value. *)
Fixpoint fold_m
  {F S T : Type}
  (f     : S -> T -> t F S)
  (x     : S)
  (ts    : list T)
: t F S :=
  match ts with
  | nil       => Success x
  | cons y ys => f x y >>= (fun r => fold_m f r ys)
  end.

(** If [fold_m] fails with [e], then there's some [x] and [y] such that [f x y = Failure e]. *)
Theorem fold_failure : forall
  (F S T : Type)
  (f     : S -> T -> t F S)
  (ts    : list T)
  (s     : S)
  (e     : F),
  fold_m f s ts = Failure e ->
    exists x y, f x y = Failure e.
Proof.
  intros F S T f.
  induction ts as [|th tr].
    intros; inversion H.
    intros.
    simpl in H.
    destruct (bind_inversion_failure _ _ _ _ _ e H) as [H_invL|H_invR].
      exists s.
        exists th.
          assumption.
      destruct H_invR as [s0 Hs0].
      apply (IHtr s0 e Hs0).
Qed.

(** If [fold_m] succeeds with [z], then either the list was empty or there's some
    [x] and [y] such that [f x y = Success z]. *)
Theorem fold_success : forall
  (F S T : Type)
  (f     : S -> T -> t F S)
  (ts    : list T)
  (s z   : S),
  fold_m f s ts = Success z ->
    ts = nil \/ exists x y, f x y = Success z.
Proof.
  intros F S T f.
  induction ts as [|th tr].
    intros. left; reflexivity.
    intros.
    simpl in H.
    destruct (bind_inversion _ _ _ _ _ _ H) as [y Hy].
      destruct Hy as [HyL HyR].
        destruct tr as [|trh trr].
          simpl in HyR.
          rewrite HyR in HyL.
          right. exists s. exists th. assumption.
          destruct (IHtr y z HyR) as [IHtrL|IHtrR].
            discriminate.
            right. assumption.
Qed.

(** Apply [f] to each element of [ts] until [f] returns [Some]. *)
Fixpoint find_m
  {F S T : Type}
  (f     : S -> t F (option T))
  (ts    : list S)
: t F (option T) :=
  match ts with
  | nil       => Success None
  | cons y ys =>
    match f y with
    | Failure e => Failure e
    | Success s =>
      match s with
      | Some x => Success (Some x)
      | None   => find_m f ys
      end
    end
  end.

(** A stronger version of [find_m] where [f] is also given a proof
    that [x] is in [xs]. *)
Definition find_m_in
  {F S T : Type}
  (xs    : list S)
  (f     : { x : S | List.In x xs } -> t F (option T))
: t F (option T) :=
  find_m f (ListAux.in_list xs).

(** If [find_m] fails with [e], then there's some [x] such that [f x = Failure e]. *)
Theorem find_failure : forall
  (F S T : Type)
  (f     : S -> t F (option T))
  (xs    : list S)
  (e     : F),
  find_m f xs = Failure e ->
    exists x, f x = Failure e.
Proof.
  intros F S T f.
  induction xs as [|xh xr].
    intros. inversion H.
    intros.
    simpl in H.
    remember (f xh) as Hfxh.
    destruct Hfxh.
    remember o as p.
    destruct p.
    discriminate.
    apply (IHxr e H).
    exists xh.
    rewrite <- HeqHfxh.
    assumption.
Qed.

(** If [find_m] succeeds with [Some t], then there's some [x] such that [f x = Success (Some t)]. *)
Theorem find_success_some : forall
  (F S T : Type)
  (f     : S -> t F (option T))
  (xs    : list S)
  (t     : T),
  find_m f xs = Success (Some t) ->
    exists x, f x = Success (Some t).
Proof.
  intros F S T f.
  induction xs as [|xh xr].
    intros. inversion H.
    intros.
    simpl in H.
    remember (f xh) as Hfxh.
    destruct Hfxh.
    remember o as p.
    destruct p.
    exists xh.
    rewrite <- HeqHfxh.
    rewrite H.
    reflexivity.
    apply (IHxr t0 H).
    discriminate.
Qed.

(** If [find_m] succeeds at all for a non-empty list, then there's some [s] and [x] such
    that [f x = Success s]. *)
Theorem find_success : forall
  (F S T : Type)
  (f     : S -> t F (option T))
  (xs    : list S)
  (r     : option T),
  xs <> nil ->
    find_m f xs = Success r ->
      exists s x, f x = Success s.
Proof.
  intros F S T f.
  induction xs as [|xh xr].
    intros. contradict H; reflexivity.
    intros.
    simpl in H0.
    remember (f xh) as Hfxh.
    destruct Hfxh.
    remember o as p.
    destruct p.
    exists r.
      exists xh.
        rewrite <- HeqHfxh.
        rewrite H0.
        reflexivity.
    exists None.
      exists xh.
        symmetry.
        assumption.
    discriminate.
Qed.
