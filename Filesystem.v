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
(** The virtual filesystem. *)
Require Coq.Lists.List.
Require Archive.
Require ArchiveHandler.
Require Error.
Require FilesystemOp.
Require FilesystemRef.
Require ListAux.
Require ListMapWeak.
Require ListSetWeak.
Require ListNonEmptyStack.
Require ListStack.
Require MapWeak.
Require MapWeakAux.
Require PathReal.
Require PathVirtual.

Import Error.Notations.
Import ListAux.Notations.

(** Abbreviations. *)
Module FOp  := FilesystemOp.
Module FRef := FilesystemRef.

Open Scope error_monad_scope.
Open Scope list_scope.

(** This file is broken into a [Signature] and [Implementation] section. The
[Signature] type documents the interface exposed by filesystem implementations
and the [Implementation] type documents the expected semantics of the
implementations. The semantics are given in terms of pure functional programs
with additional proofs that these programs are correct. It is expected that this
will be enough information to derive an implementation in an imperative language
such as Java. *)
(** The interface exposed by filesystem implementations. *)
Module Type Signature.

(** The type of filesystems. *)
Parameter t : Type.

(** Initialize a filesystem using the directory [p] in which to search for archive files. *)
Parameter make_with_path : forall (p : PathReal.t), t.

(** Initialize a filesystem without specifying an archive directory. *)
Parameter make : unit -> t.

(** Obtain a reference to the file or directory at the given [p]. Returns:
- [Success (Some r)] where [r] is a reference to the file or directory, if it exists.
- [Success None] if the file or directory does not exist.
- [Failure e] for some [e], if the object does not exist or if an I/O or other error occurs. *)
Parameter lookup : forall (p : PathVirtual.t) (f : t), FOp.t (option FRef.t).

(** Create a directory [p], including all ancestors of [p] if necessary. *)
Parameter create_directory : forall (p : PathVirtual.t) (f : t), FOp.t t.

(** Mount the archive named [a] at [p]. *)
Parameter mount : forall (p : PathVirtual.t) (a : Names.t) (f : t), FOp.t t.

End Signature.

(** The expected semantics of filesystem implementations. *)
Module Implementation : Signature.

Module Stacks := ListNonEmptyStack.Make.
Module PVS    := PathVirtual.Sets.
Module PVM    := PathVirtual.Maps.
Module PVMA   := MapWeakAux.Make (PVM).
Module E      := Error.

(** Filesystems maintain the following state: *)
Inductive fs := Filesystem {

  (** A set of explicitly-created virtual directories... *)
  fs_directories : PVS.t;

  (** ... of which [root] is always a member, and: *)
  fs_directories_root : PVS.is_in PathVirtual.root fs_directories;

  (** A set of mappings from virtual paths to non-empty stacks of archives... *)
  fs_mounts : PVM.t (Stacks.t Archive.t);

  (** ... such that each the mount path of each archive in the stack matches
      that of the key with which the stack is associated in the map. *)
  fs_mounts_paths :
    PVM.for_all_mappings (fun k s =>
      Stacks.for_all (fun a => Archive.mount_path a = k) s) fs_mounts;

  (** Optionally, the name of a directory containing archive files. *)
  fs_archive_path : option PathReal.t;

  (** A list of archive type handlers. *)
  fs_handlers : list ArchiveHandler.t
}.

Definition t := fs.

(** In order to provide the required semantics for [mount], filesystems need to
distinguish between directories provided by archives, and directories created
explicitly with [create_directory]. *)
Inductive fs_ref : Set :=
  | FSRFile             : PathVirtual.t -> fs_ref
  | FSRDirectoryArchive : PathVirtual.t -> fs_ref
  | FSRDirectoryCreated : PathVirtual.t -> fs_ref.

(** Each reference holds the path to the object. *)
Definition fs_ref_path (f : fs_ref) : PathVirtual.t :=
  match f with
  | FSRFile p             => p
  | FSRDirectoryArchive p => p
  | FSRDirectoryCreated p => p
  end.

(** There is a straightforward translation from internal filesystem references
to [FRef.t]. *)
Definition fs_ref_convert (r : fs_ref) : FRef.t :=
  match r with
  | FSRFile p             => FRef.FSFile p 
  | FSRDirectoryArchive p => FRef.FSDirectory p
  | FSRDirectoryCreated p => FRef.FSDirectory p
  end.

(** The conversion maintains the correct paths. *)
Theorem fs_ref_convert_correct : forall
  (f : fs_ref)
  (p : PathVirtual.t),
  fs_ref_path f = FRef.path (fs_ref_convert f).
Proof.
  destruct f; reflexivity.
Qed.

(** Construct a new filesystem using [p] as the directory in which to look for archives. *)
Definition make_with_path (p : PathReal.t) : t.
Proof.
  refine (Filesystem
    (PVS.singleton PathVirtual.root)
    _
    (@PVM.empty (Stacks.t Archive.t))
    _
    (Some p)
    ArchiveHandler.handlers).

  destruct (PathVirtual.eq_decidable PathVirtual.root p) as [Heq|Hneq].
    rewrite Heq.
    rewrite PVS.singleton_eq; apply (PVS.insert_is_in p).
    rewrite PVS.singleton_eq; apply (PVS.insert_is_in PathVirtual.root).

  apply PVM.for_all_mappings_empty.
Qed.

(** Construct a new filesystem without a directory in which to look for archives. *)
Definition make (_ : unit) : t.
Proof.
  refine (Filesystem
    (PVS.singleton PathVirtual.root)
    _
    (@PVM.empty (Stacks.t Archive.t))
    _
    None
    ArchiveHandler.handlers).

  rewrite PVS.singleton_eq; apply (PVS.insert_is_in PathVirtual.root).

  apply PVM.for_all_mappings_empty.
Qed.

Definition is_mounted_at
  (p : PathVirtual.t)
  (a : Archive.t)
  (f : fs)
: Prop :=
  match PVM.lookup p (fs_mounts f) with
  | Some s => Stacks.is_in a s
  | None   => False
  end.

(** File lookups. *)
Module Type LookupInterface.
  Parameter lookup          : forall (p : PathVirtual.t) (f : t), FOp.t (option FRef.t).
  Parameter lookup_internal : forall (p : PathVirtual.t) (f : t), FOp.t (option fs_ref).

Parameter lookup_internal_path : forall
  (p : PathVirtual.t)
  (f : fs)
  (r : fs_ref),
  lookup_internal p f = E.Success (Some r) -> fs_ref_path r = p.

Parameter lookup_internal_created : forall
  (p : PathVirtual.t)
  (f : fs),
  PVS.is_in p (fs_directories f) ->
    lookup_internal p f = E.Success (Some (FSRDirectoryCreated p)).

Parameter lookup_internal_root : forall
  (f : fs),
  lookup_internal PathVirtual.root f =
    E.Success (Some (FSRDirectoryCreated PathVirtual.root)).

Parameter lookup_path : forall
  (p : PathVirtual.t)
  (f : fs)
  (r : FRef.t),
  lookup p f = E.Success (Some r) -> FRef.path r = p.

Parameter lookup_root : forall
  (f : fs),
  lookup PathVirtual.root f =
    E.Success (Some (FRef.FSDirectory PathVirtual.root)).

End LookupInterface.
Module Lookup : LookupInterface.

(** Attempt to lookup [p] in [a], classifying the result. *)
Definition lookup_internal_in_archive
  (p : PathVirtual.t)
  (a : { a : Archive.t | Archive.contains p a })
: FOp.t (option fs_ref) :=
  match a with
  | exist a _ =>
    let arc_m := Archive.mount_path a         in
    let arc_p := PathVirtual.subtract p arc_m in
      (Archive.lookup a) arc_p >>= (fun r =>
        match r with
        | None   => E.Success None
        | Some r =>
          match r with
          | FRef.FSFile rp      => E.Success (Some (FSRFile (arc_m ++ rp)))
          | FRef.FSDirectory rp => E.Success (Some (FSRDirectoryArchive (arc_m ++ rp)))
          end
        end)
  end.

(** Looking up the root directory always succeeds. *)
Theorem lookup_internal_in_archive_root : forall
  (a : { a : Archive.t | Archive.contains PathVirtual.root a }),
  lookup_internal_in_archive PathVirtual.root a =
    E.Success (Some (FSRDirectoryArchive PathVirtual.root)).
Proof.
  intros.
  unfold lookup_internal_in_archive.
  destruct a as [a Ha].
  unfold Archive.contains in Ha.
  assert (Archive.mount_path a = PathVirtual.root) as H_root.
    apply (PathVirtual.contains_is_root).
    assumption.

  rewrite H_root.
  rewrite PathVirtual.subtract_root.
  rewrite Archive.lookup_root.
  reflexivity.
Qed.

(** The paths returned inside references will always match the original path. *)
Theorem lookup_internal_in_archive_same : forall
  (p  : PathVirtual.t)
  (a  : { a : Archive.t | Archive.contains p a })
  (r  : fs_ref),
  lookup_internal_in_archive p a = E.Success (Some r) ->
    fs_ref_path r = p.
Proof.
  intros p a r H_succ.
  destruct a as [a Hc].
  unfold Archive.contains           in Hc.
  unfold lookup_internal_in_archive in H_succ.
  remember (PathVirtual.subtract p (Archive.mount_path a)) as H_psubm.

  destruct (E.bind_inversion _ _ _ _ _ _ H_succ) as [opt_r Hinv].
  clear H_succ.
  destruct Hinv as [Hinv_L Hinv_R].
  destruct opt_r as [some_r|].
  destruct some_r as [rp|rp].

  (*
   For each of the possible [lookup] cases, it's necessary to
   show that [(Archive.mount_path a) ++ rp = p], where [rp] is
   the path in the returned reference.
  *)

  cut ((Archive.mount_path a) ++ rp = p).
    intros Hrpe.
    rewrite Hrpe in Hinv_R.
    injection Hinv_R.
    intros H_inj.
    rewrite <- H_inj.
    reflexivity.

    pose proof (Archive.lookup_same a H_psubm _ Hinv_L) as H_lookup_same.
    simpl in H_lookup_same.
    pose proof (PathVirtual.contains_subtract_id _ _ Hc) as H_app.
    rewrite H_lookup_same.
    rewrite HeqH_psubm.
    assumption.

  cut ((Archive.mount_path a) ++ rp = p).
    intros Hrpe.
    rewrite Hrpe in Hinv_R.
    injection Hinv_R.
    intros H_inj.
    rewrite <- H_inj.
    reflexivity.  

    pose proof (Archive.lookup_same a H_psubm _ Hinv_L) as H_lookup_same.
    simpl in H_lookup_same.
    pose proof (PathVirtual.contains_subtract_id _ _ Hc) as H_app.
    rewrite H_lookup_same.
    rewrite HeqH_psubm.
    assumption.

  discriminate.
Qed.

Definition archive_contains_iter
  (s  : Stacks.t Archive.t)
  (p  : PathVirtual.t)
  (f  : forall x, List.In x (Stacks.peek_list s) -> Archive.contains p x)
  (ap : { x : Archive.t | List.In x (Stacks.peek_list s) })
: { x : Archive.t | Archive.contains p x } :=
  match ap with
  | exist x p => exist _ x (f x p)
  end.

Definition stacks_contains_forall_function : forall
  (p  : PathVirtual.t)
  (s  : Stacks.t Archive.t)
  (Hc : Stacks.for_all (Archive.contains p) s),
  (forall a : Archive.t, List.In a (Stacks.peek_list s) -> Archive.contains p a).
Proof.
  intros.
  destruct (Stacks.for_all_peek (Archive.contains p) s) as [HfaL HfaR].
  pose proof (HfaL Hc) as Hlfa.
  clear HfaL.
  clear HfaR.

  destruct (List.Forall_forall (Archive.contains p) (Stacks.peek_list s)) as [HfaL HfaR].
  pose proof (HfaL Hlfa) as Hlistfa.
  clear HfaL.
  clear HfaR.
  clear Hlfa.

  apply Hlistfa.
  assumption.
Qed.

(** Try to obtain a reference to the file or directory named by [p]
in the given archive stack [s]. *)
Definition lookup_internal_in_archives
  (p  : PathVirtual.t)
  (s  : Stacks.t Archive.t)
  (Hc : Stacks.for_all (Archive.contains p) s)
: FOp.t (option fs_ref) :=
  let stack    := ListAux.in_list (Stacks.peek_list s)                                                in
  let archives := List.map (archive_contains_iter s p (stacks_contains_forall_function p s Hc)) stack in
    E.find_m (lookup_internal_in_archive p) archives.

(** The paths returned inside references will always match the original path. *)
Theorem lookup_internal_in_archives_same : forall
  (p  : PathVirtual.t)
  (s  : Stacks.t Archive.t)
  (Hc : Stacks.for_all (Archive.contains p) s)
  (r  : fs_ref),
  lookup_internal_in_archives p s Hc = E.Success (Some r) ->
    fs_ref_path r = p.
Proof.
  intros p s Hc r H_succ.
  unfold lookup_internal_in_archives in H_succ.

  remember (lookup_internal_in_archive p) as Hf.
  remember (ListAux.in_list (Stacks.peek_list s)) as H_stack.
  remember (List.map (archive_contains_iter s p (stacks_contains_forall_function p s Hc)) H_stack) as H_arcs.

  assert (H_arcs <> nil) as H_arcs_not_nil.
    rewrite HeqH_arcs.
    apply ListAux.map_preserves_not_nil.
    rewrite HeqH_stack.
    apply ListAux.in_list_preserves_not_nil.
    apply Stacks.peek_list_not_empty.

  destruct (Error.find_success_some _ _ _ Hf H_arcs r H_succ) as [k Hk].
  rewrite HeqHf in Hk.
  apply (lookup_internal_in_archive_same p k r Hk).
Qed.

(** Looking up the root directory always succeeds. *)
Theorem lookup_internal_in_archives_root : forall
  (s  : Stacks.t Archive.t)
  (Hc : Stacks.for_all (Archive.contains PathVirtual.root) s),
  lookup_internal_in_archives PathVirtual.root s Hc =
    E.Success (Some (FSRDirectoryArchive PathVirtual.root)).
Proof.
  intros.
  unfold lookup_internal_in_archives.

  remember (lookup_internal_in_archive PathVirtual.root) as Hf.
  remember (ListAux.in_list (Stacks.peek_list s)) as H_stack.
  remember (List.map (archive_contains_iter s PathVirtual.root
    (stacks_contains_forall_function PathVirtual.root s Hc)) H_stack) as H_arcs.

  assert (H_arcs <> nil) as H_arcs_not_nil.
    rewrite HeqH_arcs.
    apply ListAux.map_preserves_not_nil.
    rewrite HeqH_stack.
    apply ListAux.in_list_preserves_not_nil.
    apply Stacks.peek_list_not_empty.

  destruct H_arcs.
    contradict H_arcs_not_nil; reflexivity.
    pose proof (lookup_internal_in_archive_root s0) as H_root.
    rewrite HeqHf.
    simpl.
    rewrite H_root.
    reflexivity.
Qed.

Theorem stacks_mount_path_implies_contains : forall
  (m  : PathVirtual.t)
  (s  : Stacks.t Archive.t)
  (Hc : Stacks.for_all (fun a => Archive.mount_path a = m) s),
  Stacks.for_all (Archive.contains m) s.
Proof.
  intros.
  apply (@Stacks.for_all_implication Archive.t
    (fun a => Archive.mount_path a = m) _
    (fun a => Archive.mount_path_implies_contains m a) s Hc).
Qed.

Theorem stacks_mount_path_implies_contains_all : forall
  (m p : PathVirtual.t)
  (s   : Stacks.t Archive.t)
  (Hpc : PathVirtual.contains m p)
  (Hac : Stacks.for_all (Archive.contains m) s),
  Stacks.for_all (Archive.contains p) s.
Proof.
  intros.
  apply (@Stacks.for_all_implication Archive.t
    (fun a => Archive.contains m a)
    (fun a => Archive.contains p a)).
    intros a Hacm.
    apply (Archive.contains_transitive p m a); assumption.
    assumption.
Qed.

(** Look up [p] in the stack of archives mounted at [m], if any. *)
Definition lookup_internal_in_mount_contains
  (p  : PathVirtual.t)
  (f  : fs)
  (m  : PathVirtual.t)
  (Hc : PathVirtual.contains m p)
: FOp.t (option fs_ref) :=
  match PVMA.lookup_ex m (fs_mounts f) with
  | Some (exist s H_maps) =>
    (** Compute a proof that all archives at [m] contain [p]. *)
    let H_contains_m     := PVM.for_all_mappings_maps _ (fs_mounts f) m _ (fs_mounts_paths f) H_maps in
    let H_contains_m_all := stacks_mount_path_implies_contains m s H_contains_m in
    let H_contains_p_all := stacks_mount_path_implies_contains_all m p s Hc H_contains_m_all in
      lookup_internal_in_archives p s H_contains_p_all
  | None => E.Success None
  end.

(** Looking up the root directory always succeeds. *)
Theorem lookup_internal_in_mount_contains_root : forall
  (f  : fs)
  (m  : PathVirtual.t)
  (Hc : PathVirtual.contains m PathVirtual.root),
  (lookup_internal_in_mount_contains PathVirtual.root f m Hc = E.Success None) \/
  (lookup_internal_in_mount_contains PathVirtual.root f m Hc =
    E.Success (Some (FSRDirectoryArchive PathVirtual.root))).
Proof.
  intros f m Hc.
  unfold lookup_internal_in_mount_contains.

  destruct (PVMA.lookup_ex m (fs_mounts f)) as [[s Hs]|].
  remember (PVM.for_all_mappings_maps _ (fs_mounts f) m _ (fs_mounts_paths f) Hs)
    as H_contains_m.
  remember (stacks_mount_path_implies_contains m s H_contains_m)
    as H_contains_m_all.
  remember (stacks_mount_path_implies_contains_all m PathVirtual.root s _ H_contains_m_all)
    as H_contains_p_all.
  rewrite (lookup_internal_in_archives_root).
  right; reflexivity.
  left; reflexivity.
Qed.

(** If [m] contains [p], check for [p - m] in the stack of archives at [m], if any. *)
Definition lookup_internal_in_mount
  (p : PathVirtual.t)
  (f : fs)
  (m : PathVirtual.t)
: FOp.t (option fs_ref) :=
  match PathVirtual.contains_decidable m p with
  | right _  => E.Success None
  | left  hc => lookup_internal_in_mount_contains p f m hc
  end.

(** The paths returned inside references will always match the original path. *)
Theorem lookup_internal_in_mount_path : forall
  (p : PathVirtual.t)
  (f : fs)
  (m : PathVirtual.t)
  r,
  lookup_internal_in_mount p f m = E.Success (Some r) ->
    fs_ref_path r = p.
Proof.
  intros p f m r H_look.
  unfold lookup_internal_in_mount in H_look.
  destruct (PathVirtual.contains_decidable m p).
  unfold lookup_internal_in_mount_contains in H_look.
  destruct (PVMA.lookup_ex m (fs_mounts f)) as [[s Hs]|].

  remember (PVM.for_all_mappings_maps _ (fs_mounts f) m _ (fs_mounts_paths f) Hs)
    as H_contains_m.
  remember (stacks_mount_path_implies_contains m s H_contains_m) 
    as H_contains_m_all.
  remember (stacks_mount_path_implies_contains_all m p s c H_contains_m_all)
    as H_contains_p_all.

  apply (lookup_internal_in_archives_same p s H_contains_p_all r H_look).
  discriminate.
  discriminate.
Qed.

(** Looking up the root directory always succeeds. *)
Theorem lookup_internal_in_mount_root : forall
  (f : fs)
  (m : PathVirtual.t),
  (lookup_internal_in_mount PathVirtual.root f m = E.Success None) \/
  (lookup_internal_in_mount PathVirtual.root f m =
    E.Success (Some (FSRDirectoryArchive PathVirtual.root))).
Proof.
  intros f m.
  unfold lookup_internal_in_mount.
  destruct (PathVirtual.contains_decidable m PathVirtual.root) as [HcL|HcR].
    destruct (lookup_internal_in_mount_contains_root f m HcL).
      rewrite H.
      left; reflexivity.
      right; rewrite H; reflexivity.
      left; reflexivity.
Qed.

(** Check all archives for the given [p]. Only archives that are mounted
at paths that contain (according to [PathVirtual.contains]) the given [p]
are checked. *)
Definition lookup_internal_in_mounts
  (p : PathVirtual.t)
  (f : fs)
: FOp.t (option fs_ref) :=
  E.find_m (lookup_internal_in_mount p f) (PVM.keys (fs_mounts f)).

(** The paths returned inside references will always match the original path. *)
Theorem lookup_internal_in_mounts_path : forall
  (p : PathVirtual.t)
  (f : fs)
  r,
  lookup_internal_in_mounts p f = E.Success (Some r) ->
    fs_ref_path r = p.
Proof.
  intros until r.
  unfold lookup_internal_in_mounts.
  remember (PVM.keys (fs_mounts f))       as H_mounts.
  remember (lookup_internal_in_mount p f) as H_look.
  intros H_find.
  destruct (E.find_success_some _ _ _ H_look H_mounts r H_find).
  rewrite HeqH_look in H.
  apply (lookup_internal_in_mount_path p f x r H).
Qed.

(** Looking up the root directory always succeeds. *)
Theorem lookup_internal_in_mounts_root : forall (f : fs),
  (lookup_internal_in_mounts PathVirtual.root f = E.Success None) \/
  (lookup_internal_in_mounts PathVirtual.root f =
    E.Success (Some (FSRDirectoryArchive PathVirtual.root))).
Proof.
  intros f.
  unfold lookup_internal_in_mounts.
  induction (PVM.keys (fs_mounts f)) as [|kh kr].
    simpl. left; reflexivity.
    simpl.
    destruct (lookup_internal_in_mount_root f kh).
    rewrite H; auto.
    rewrite H; auto.
Qed.

(** Check the set of explicitly-created virtual directories for [p]. *)
Definition lookup_internal_in_directories
  (p : PathVirtual.t)
  (f : fs)
: option fs_ref :=
  match PVS.is_in_decidable p (fs_directories f) with
  | left _  => Some (FSRDirectoryCreated p)
  | right _ => None
  end.

(** The paths returned inside references will always match the original path. *)
Theorem lookup_internal_in_directories_path : forall
  (p : PathVirtual.t)
  (f : fs)
  r,
  lookup_internal_in_directories p f = (Some r) ->
    fs_ref_path r = p.
Proof.
  intros p f r.
  unfold lookup_internal_in_directories.
  intros H_look.
  destruct (PVS.is_in_decidable p).
  injection H_look.
  intros H_eq.
  rewrite <- H_eq.
  reflexivity.
  discriminate.
Qed.

(** Looking up [root] always succeeds and returns a created directory. *)
Theorem lookup_internal_in_directories_root : forall (f : fs),
  lookup_internal_in_directories PathVirtual.root f =
    Some (FSRDirectoryCreated PathVirtual.root).
Proof.
  intros f.
  unfold lookup_internal_in_directories.
  destruct (PVS.is_in_decidable PathVirtual.root (fs_directories f)).
    reflexivity.
    contradict n.
      exact (fs_directories_root f).
Qed.

(** Check all relevant archives and virtual directories for [p].
Note that if a directory exists in an archive and also exists in the list
of explicitly created directories, the explicitly created one takes precedence. *)
Definition lookup_internal_direct
  (p : PathVirtual.t)
  (f : fs)
: FOp.t (option fs_ref) :=
  lookup_internal_in_mounts p f >>= (fun opt =>
    match opt with
    | None   => E.Success (lookup_internal_in_directories p f)
    | Some r =>
      match r with
      | FSRDirectoryArchive p => E.Success (lookup_internal_in_directories p f)
      | FSRDirectoryCreated p => E.Success (lookup_internal_in_directories p f)
      | FSRFile             p => E.Success opt
      end
    end).

(** The paths returned inside references will always match the original path. *)
Theorem lookup_internal_direct_path : forall
  (p : PathVirtual.t)
  (f : fs)
  r,
  lookup_internal_direct p f = E.Success (Some r) ->
    fs_ref_path r = p.
Proof.
  intros p f r.
  unfold lookup_internal_direct.
  intros H_look.
  destruct (E.bind_inversion _ _ _ _ _ _ H_look) as [rr H_invR].
  destruct H_invR as [H_invRL H_invRR].
    rewrite H_invRL in H_look.
    simpl in *.
    destruct rr.
    destruct f0.
    rewrite H_invRR in H_invRL.
    apply (lookup_internal_in_mounts_path p f r H_invRL).

    injection H_invRR.
    intros H_eq.
    pose proof (lookup_internal_in_directories_path t0 f r H_eq) as H_dp.
    pose proof (lookup_internal_in_mounts_path p f (FSRDirectoryArchive t0) H_invRL) as H_eq2.
    rewrite <- H_dp in H_eq2.
    assumption.

    injection H_invRR.
    intros H_eq.
    pose proof (lookup_internal_in_directories_path t0 f r H_eq) as H_dp.
    pose proof (lookup_internal_in_mounts_path p f (FSRDirectoryCreated t0) H_invRL) as H_eq2.
    rewrite <- H_dp in H_eq2.
    assumption.

    injection H_invRR.
    intros H_eq.
    apply (lookup_internal_in_directories_path p f r H_eq).
Qed.

(** Check that the given [p] is a directory and fail if it isn't. *)
Definition check_directory
  (p : PathVirtual.t)
  (f : fs)
: FOp.t unit :=
  match lookup_internal_direct p f with
  | E.Failure e        => E.Failure e
  | E.Success None     => E.Failure FOp.Error_Nonexistent
  | E.Success (Some r) =>
    match r with
    | FSRFile _             => E.Failure FOp.Error_Not_A_Directory
    | FSRDirectoryArchive _ => E.Success tt
    | FSRDirectoryCreated _ => E.Success tt
    end
  end.

(** Check that all of the ancestors of [p] are directories. *)
Definition check_ancestor_directories
  (p : PathVirtual.t)
  (f : fs)
: FOp.t unit :=
  E.fold_m (fun _ ancestor => check_directory ancestor f)
    tt (PathVirtual.Enumeration.enumeration p).

(** Look up [p] in the filesystem, first checking if all ancestors of [p]
exist and are directories. *)
Definition lookup_internal
  (p : PathVirtual.t)
  (f : fs)
: FOp.t (option fs_ref) :=
  check_ancestor_directories p f >> lookup_internal_direct p f.

(** The paths returned inside references will always match the original path. *)
Theorem lookup_internal_path : forall
  (p : PathVirtual.t)
  (f : fs)
  r,
  lookup_internal p f = E.Success (Some r) ->
    fs_ref_path r = p.
Proof.
  intros p f r.
  unfold lookup_internal.
  intros H_look.
  destruct (E.bind_inversion _ _ _ _ _ _ H_look) as [rr H_invR].
  destruct H_invR as [H_invRL H_invRR].
  apply (lookup_internal_direct_path p f r H_invRR).
Qed.

(** Looking up [root] always succeeds and returns a created directory. *)
Theorem lookup_internal_root : forall
  (f : fs),
  lookup_internal PathVirtual.root f =
    E.Success (Some (FSRDirectoryCreated PathVirtual.root)).
Proof.
  intros f.
  unfold lookup_internal.
  simpl.
  unfold lookup_internal_direct.
  destruct (lookup_internal_in_mounts_root f) as [Hn|Hs].
    rewrite Hn.
    simpl.
    rewrite (lookup_internal_in_directories_root f).
    reflexivity.

    rewrite Hs.
    simpl.
    rewrite (lookup_internal_in_directories_root f).
    reflexivity.
Qed.

(** If [p] is in the filesystem's set of directories, [p] will always be returned
    as a created directory. *)
Theorem lookup_internal_created : forall
  (p : PathVirtual.t)
  (f : fs),
  PVS.is_in p (fs_directories f) ->
    lookup_internal p f = E.Success (Some (FSRDirectoryCreated p)).
Proof.
  intros p f H_in.
Admitted.

Definition lookup
  (p : PathVirtual.t)
  (f : fs)
: FOp.t (option FRef.t) :=
  lookup_internal p f >>= (fun opt =>
    match opt with
    | Some r => E.Success (Some (fs_ref_convert r))
    | None   => E.Success None
    end).

(** The paths returned inside references will always match the original path. *)
Theorem lookup_path : forall
  (p : PathVirtual.t)
  (f : fs)
  r,
  lookup p f = E.Success (Some r) ->
    FRef.path r = p.
Proof.
  intros p f r.
  unfold lookup.
  intros H_look.
  destruct (E.bind_inversion _ _ _ _ _ _ H_look) as [rr H_invR].
  destruct H_invR as [H_invRL H_invRR].
  destruct rr.

  injection H_invRR.
  intros H_eq.
  rewrite <- H_eq.
  rewrite <- fs_ref_convert_correct.

  apply (lookup_internal_path p f f0 H_invRL).
  auto.
  discriminate.
Qed.

(** Looking up [root] always succeeds and returns a created directory. *)
Theorem lookup_root : forall (f : fs),
  lookup PathVirtual.root f =
    E.Success (Some (FRef.FSDirectory PathVirtual.root)).
Proof.
  intros f.
  unfold lookup.
  rewrite (lookup_internal_root f).
  reflexivity.
Qed.

End Lookup.

(** Directory creation. *)
Module Type CreateDirectoryInterface.
  Parameter create_directory : forall (p : PathVirtual.t) (f : t), FOp.t t.

Parameter create_directory_created : forall p f g,
  create_directory p f = E.Success g ->
    Lookup.lookup_internal p g = E.Success (Some (FSRDirectoryCreated p)).

End CreateDirectoryInterface.
Module CreateDirectory : CreateDirectoryInterface.

(** Add the directory [p] to the set of virtual directories in [f]. *)
Definition create_directory_insert
  (p : PathVirtual.t)
  (f : fs)
: fs.
Proof.
  refine (Filesystem
    (PVS.insert p (fs_directories f))
    _
    (fs_mounts f)
    (fs_mounts_paths f)
    (fs_archive_path f)
    (fs_handlers f)).

  destruct (PathVirtual.eq_decidable PathVirtual.root p) as [Heq|Hneq].
    rewrite Heq.
    apply (PVS.insert_is_in p (fs_directories f)).
    apply (PVS.insert_preserves_is_in PathVirtual.root p (fs_directories f) Hneq (fs_directories_root f)).
Defined.

(** An inserted directory is definitely inserted. *)
Theorem create_directory_inserted : forall
  (p : PathVirtual.t)
  (f : fs),
  PVS.is_in p (fs_directories (create_directory_insert p f)).
Proof.
  intros.
  apply (PVS.insert_is_in).
Qed.

Definition create_directory_internal_actual
  (f : fs)
  (p : PathVirtual.t)
: FOp.t t :=
  Lookup.lookup_internal p f >>= (fun opt =>
    match opt with
    | None   => E.Success (create_directory_insert p f)
    | Some r =>
      match r with
      | FSRFile _             => E.Failure FOp.Error_Not_A_Directory
      | FSRDirectoryArchive _ => E.Success f
      | FSRDirectoryCreated _ => E.Success f
      end
    end).

Theorem create_directory_internal_actual_create : forall f p g,
  create_directory_internal_actual f p = E.Success g ->
    Lookup.lookup_internal p g = E.Success (Some (FSRDirectoryCreated p)) \/
    Lookup.lookup_internal p g = E.Success (Some (FSRDirectoryArchive p)).
Proof.
  intros f p g H_create.
  destruct (E.bind_inversion _ _ _ _ _ _ H_create) as [h [HL HR]].
  destruct h.
  destruct f0.
  discriminate.

  injection HR.
  intros Hfg.
  rewrite <- Hfg.

  right.
    pose proof (Lookup.lookup_internal_path p f (FSRDirectoryArchive t0) HL) as H_path.
    simpl in H_path.
    rewrite <- H_path.
    rewrite <- H_path in HL.
    assumption.

  injection HR.
  intros Hfg.
  rewrite <- Hfg.

  left.
    pose proof (Lookup.lookup_internal_path p f (FSRDirectoryCreated t0) HL) as H_path.
    simpl in H_path.
    rewrite <- H_path.
    rewrite <- H_path in HL.
    assumption.

  injection HR.
  intros Hfg.
  rewrite <- Hfg.

  pose proof (create_directory_inserted p f).
  left. apply (Lookup.lookup_internal_created p _ H).
Qed.

Definition create_directory
  (p : PathVirtual.t)
  (f : fs)
: FOp.t t :=
  E.fold_m create_directory_internal_actual f (PathVirtual.Enumeration.enumeration p).

Theorem create_directory_created : forall p f g,
  create_directory p f = E.Success g ->
    Lookup.lookup_internal p g = E.Success (Some (FSRDirectoryCreated p)).
Proof.
  intros p f g.
  unfold create_directory.
  intros H_fold.
  destruct (E.fold_success _ _ _ _ _ _ _ H_fold) as [H_fsl|H_fsr].
    rewrite (PathVirtual.Enumeration.enumeration_is_root p H_fsl).
    rewrite (Lookup.lookup_internal_root g).
    reflexivity.
    simpl.
    induction (PathVirtual.Enumeration.enumeration p) as [|eh er].
Admitted.

End CreateDirectory.

(** Archive mounting. *)
Module Type MountInterface.
  Parameter mount : forall (p : PathVirtual.t) (a : Names.t) (f : t), FOp.t t.
End MountInterface.
Module Mount : MountInterface.

(** Determine whether or not the given mount point is a directory. If it is,
determine if it is provided by an archive or was explicitly created. If it
was provided by an archive, explicitly create it. *)
Definition mount_check_point
  (p : PathVirtual.t)
  (f : fs)
: FOp.t t :=
  Lookup.lookup_internal p f >>= (fun opt =>
    match opt with
    | Some (FSRFile r)             => E.Failure FOp.Error_Not_A_Directory
    | Some (FSRDirectoryArchive p) => CreateDirectory.create_directory p f
    | Some (FSRDirectoryCreated p) => E.Success f
    | None                         => E.Failure FOp.Error_Nonexistent
    end).

Theorem mount_check_point_directory : forall p f g,
  mount_check_point p f = E.Success g ->
    Lookup.lookup_internal p g = E.Success (Some (FSRDirectoryCreated p)).
Proof.
  intros p f g H_check.
  destruct (E.bind_inversion _ _ _ _ _ _ H_check) as [opt [HbL HbR]].
  destruct opt.
  destruct f0.
    discriminate.
    assert (t0 = p) as H_eq.
      pose proof (Lookup.lookup_internal_path p f (FSRDirectoryArchive t0) HbL).
      assumption.
    rewrite <- H_eq.
    apply (CreateDirectory.create_directory_created t0 f g HbR).

    assert (t0 = p) as H_eq.
      pose proof (Lookup.lookup_internal_path p f (FSRDirectoryCreated t0) HbL).
      assumption.
    injection HbR; intros H_eq2.
    rewrite <- H_eq in *.
    rewrite <- H_eq2.
    assumption.

    discriminate.
Qed.

(** Mount the archive named [a], setting [m] as the mount point for the archive,
failing immediately if the given filesystem does not have a defined archive
directory. *)
Definition mount_load_archive
  (a : Names.t)
  (m : PathVirtual.t)
  (f : fs)
: FOp.t Archive.t :=
  match fs_archive_path f with
  | None   => E.Failure FOp.Error_Nonexistent
  | Some d => ArchiveHandler.handle (fs_handlers f) (d @@ a) m 
  end.

(** Loaded archives have the correct mount paths. *)
Theorem mount_load_archive_path : forall
  (a : Names.t)
  (m : PathVirtual.t)
  (f : fs)
  (r : Archive.t),
  mount_load_archive a m f = E.Success r ->
    Archive.mount_path r = m.
Proof.
  intros until r.
  unfold mount_load_archive.
  destruct (fs_archive_path f).
    induction (fs_handlers f) as [|fh fr].
      intros; discriminate.
      simpl. destruct (ArchiveHandler.can_handle fh (t0 @@ a)).
        intros.
        apply (ArchiveHandler.load_path_correct fh (t0 @@ a) m r H).
        apply IHfr.
      intros; discriminate.
Qed.

(** If the mount [p] exists, push [a] onto the stack of archives. Otherwise,
create a new archive stack at [p] consisting of [a]. *)
Definition mount_push_or_singleton
  (a  : Archive.t)
  (p  : PathVirtual.t)
  (ms : PVM.t (Stacks.t Archive.t))
  (Hm : Archive.mount_path a = p)
: PVM.t (Stacks.t Archive.t) :=
  match PVMA.lookup_ex p ms with
  | Some (exist stack _) => PVM.insert p (Stacks.push a stack) ms
  | None                 => PVM.insert p (Stacks.singleton a) ms
  end.

(** [mount_push_or_singleton] is correct. *)
Theorem mount_push_or_singleton_is_in : forall
  (a  : Archive.t)
  (p  : PathVirtual.t)
  (ms : PVM.t (Stacks.t Archive.t))
  (Hm : Archive.mount_path a = p),
  exists (s : Stacks.t Archive.t),
    PVM.key_maps_to p s (mount_push_or_singleton a p ms Hm) /\ Stacks.is_in a s.
Proof.
  intros.
  unfold mount_push_or_singleton.
  remember (PVMA.lookup_ex p ms) as H_look.
  destruct H_look.
  destruct s as [x Hx].
  exists (Stacks.push a x).
    split.
    apply (PVM.insert_maps_to p (Stacks.push a x) ms).
    apply (Stacks.push_in a x).
  exists (Stacks.singleton a).
    split.
    apply (PVM.insert_maps_to p (Stacks.singleton a) ms).
    apply (Stacks.singleton_in a).
Qed.

(** Inserted the loaded archive [a] at [p]. This function simply calculates
    proofs, the actual "insert" semantics are given in [mount_push_or_singleton]. *)
Definition mount_insert_archive
  (p  : PathVirtual.t)
  (f  : fs)
  (a  : Archive.t)
  (Hm : Archive.mount_path a = p)
: fs.
Proof.
  refine (
    Filesystem
      (fs_directories f)
      (fs_directories_root f)
      (mount_push_or_singleton a p (fs_mounts f) Hm)
      _
      (fs_archive_path f)
      (fs_handlers f)
  ).

  unfold mount_push_or_singleton.
  destruct (PVMA.lookup_ex p (fs_mounts f)) as [some|none].
    destruct some as [s_existing H_p_maps_existing].

    (** First, show that the paths are correct in the existing stack. *)
    pose proof (fs_mounts_paths f)
      as H_existing_mappings_all.
    pose proof (PVM.for_all_mappings_maps _ (fs_mounts f) _ _ H_existing_mappings_all H_p_maps_existing)
      as H_existing_stack_prop.
    (** Then, given that the path is correct in the pushed archive, [P]
        holds for the new stack. *)
    pose proof (Stacks.for_all_push _ s_existing a H_existing_stack_prop Hm)
      as H_pushed_stack_prop.
    (** [P] held for the original map, and it holds for the new stack,
        so it holds for the new map. *)
    apply PVM.for_all_mappings_insert.
    assumption.
    assumption.

    (** In this case, the stack being inserted is a singleton. If [P]
        holds for the archive, it holds for the singleton. *)
    pose proof (Stacks.for_all_singleton (fun a => Archive.mount_path a = p) a Hm)
      as H_singleton.
    pose proof (fs_mounts_paths f)
      as H_existing_mappings_all.
    (** [P] held for the original map, and it holds for the new stack,
        so it holds for the new map. *)
    apply PVM.for_all_mappings_insert.
    assumption.
    assumption.
Defined.

Definition mount
  (p : PathVirtual.t)
  (n : Names.t)
  (f : fs)
: FOp.t t :=
  mount_check_point p f >>= (fun g =>
    match mount_load_archive n p g as mla
      return (mount_load_archive n p g = mla -> FOp.t t)
    with
    | E.Failure e => fun _ => E.Failure e
    | E.Success a => fun H => E.Success (mount_insert_archive p g a (mount_load_archive_path n p g a H))
    end eq_refl).

(** A mounted archive is mounted. *)
Theorem mount_insert_archive_is_mounted : forall
  (p : PathVirtual.t)
  (f : fs)
  (a : Archive.t)
  (H : Archive.mount_path a = p),
    is_mounted_at p a (mount_insert_archive p f a H).
Proof.
  intros p f a H.
  unfold is_mounted_at.
  simpl.
  unfold mount_insert_archive.
  simpl.
  remember (mount_push_or_singleton a p (fs_mounts f) H) as H_mpush.
  destruct (mount_push_or_singleton_is_in a p (fs_mounts f) H) as [s Hs].
  destruct Hs as [HsL HsR].
  destruct (PVM.lookup_maps_to_some p s H_mpush).
  rewrite HeqH_mpush in H0.
  pose proof (H0 HsL).
  rewrite HeqH_mpush.
  rewrite H2.
  assumption.
Qed.

End Mount.

Definition lookup           := Lookup.lookup.
Definition create_directory := CreateDirectory.create_directory.
Definition mount            := Mount.mount.

End Implementation.
