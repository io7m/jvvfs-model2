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
(** The interface provided by mountable archives. *)
Require Error.
Require FilesystemOp.
Require FilesystemRef.
Require InputStream.
Require ListAux.
Require ListMapWeak.
Require ListSetWeak.
Require ListStack.
Require MapWeak.
Require PathVirtual.
Require Size.
Require Time.

Import ListAux.Notations.

Open Scope list_scope.

(** Abbreviations. *)
Module E    := Error.
Module FRef := FilesystemRef.
Module FOp  := FilesystemOp.

(** An archive is an object in the operating system filesystem that
can be "mounted" in the virtual filesystem.

An archive mounted at mount point [M] makes its contents available
at paths prefixed with [M]. As an example, if an archive contains
the file [/x/y/z/file.txt] and the archive is mounted at [/usr], then
the file is accessible via [/usr/x/y/z/file.txt] in the virtual
filesystem. The implementation is responsible for converting virtual
paths to archive-relative paths. That is, if a user tries to open
[/usr/x/y/z/file.txt] in the example above, the filesystem is
responsible for translating that to [/x/y/z/file.txt] before passing
the path to the archive interface. *)
(** The type [t] represents the internal interface exposed by archive
implementations. 

Note that the theorems included as part of the [t] type assume a
lack of catastrophic errors raised by the filesystem. This obviously
does not quite reflect reality! As an example, looking up a file in
an archive may be successful, but opening the file could then fail
if the filesystem is corrupt. The fact that this may occur is expressed
in the types of the functions (due to the fact that they are all
effectful computations in the [Error] monad) but is not expressed
in the types of the theorems (because successfully looking up a file
does not imply that the file can be opened reliably, even though a
theorem may state exactly that). The reasons for this are simplicity
and readability: repeatedly stating that each subexpression
of a theorem may fail would make them almost impossible to read. *)
Record t := MakeT {

(** The path at which the archive is mounted. *)
mount_path : PathVirtual.t;

(** Retrieve a reference to the object at the given path. This is
a "primitive" operation; all other functions should use [lookup]
internally in order to provide consistent semantics. *)
lookup : PathVirtual.t -> FOp.t (option FRef.t);

(** All archives contain [root]. *)
lookup_root : lookup PathVirtual.root = E.Success (Some (FRef.FSDirectory PathVirtual.root));

(** File objects cannot have children. *)
lookup_file_child : forall p n,
  lookup p = E.Success (Some (FRef.FSFile p)) ->
    lookup (p @@ n) = E.Failure FOp.Error_Not_A_Directory;

(** Conversely, the ancestor of any object must be a directory. *)
lookup_ancestor : forall p n o,
  lookup (p @@ n) = E.Success (Some o) ->
    lookup p = E.Success (Some (FRef.FSDirectory p));

(** The path returned by [lookup] is the same as the given path. *)
lookup_same : forall p r,
  lookup p = E.Success (Some r) ->
    FRef.path r = p;

(** List the contents of the directory at the given path. *)
directory_list : PathVirtual.t -> FOp.t (list Names.t);

(** Listing a directory works iff the target path is a directory. *)
directory_list_directory : forall p ns,
  lookup p = E.Success (Some (FRef.FSDirectory p)) <->
    directory_list p = E.Success ns;

(** Open the file at the given path. *)
file_open : PathVirtual.t -> FOp.t InputStream.t;

(** Opening a file works iff the target path is a file. *)
file_open_file : forall p i,
  lookup p = E.Success (Some (FRef.FSFile p)) <->
    file_open p = E.Success i;

(** Retrieve the size in bytes of the file at the given path. *)
file_size : PathVirtual.t -> FOp.t Size.t;

(** Retrieving the size of a file works iff the target path is a file. *)
file_size_file : forall p s,
  lookup p = E.Success (Some (FRef.FSFile p)) <->
    file_size p = E.Success s;

(** Retrieve the modification time of the file at the given path. *)
file_mtime : PathVirtual.t -> FOp.t Time.t;

(** Retrieving the modification time of a file works iff the target path is a file. *)
file_mtime_file : forall p t,
  lookup p = E.Success (Some (FRef.FSFile p)) <->
    file_mtime p = E.Success t;

(** Close the given archive, freeing any resources. *) 
close : unit -> FOp.t unit

}.

(** The archive [a] is mounted at a path that contains [p]. *)
Definition contains
  (p : PathVirtual.t)
  (a : t)
: Prop :=
  PathVirtual.contains (mount_path a) p.

(** It naturally follows that if [mount_path a = p], then [contains p a]. *)
Theorem mount_path_implies_contains : forall
  (p : PathVirtual.t)
  (a : t),
  mount_path a = p -> contains p a.
Proof.
  intros p a Heq.
  unfold contains.
  unfold PathVirtual.contains.
  left; assumption.
Qed.

(** And obviously, [PathVirtual.contains m p] -> [contains m a] -> [contains p a]. *)
Theorem contains_transitive : forall
  (p m : PathVirtual.t)
  (a   : t),
  PathVirtual.contains m p -> contains m a -> contains p a.
Proof.
  intros p m a Hcmp Hcma.
  unfold contains in *.
  apply (PathVirtual.contains_trans (mount_path a) m p); assumption.
Qed.
