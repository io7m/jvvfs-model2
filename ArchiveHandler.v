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
(** The archive handler, mapping file types to archive implementations. *)
Require Archive.
Require Error.
Require FilesystemOp.
Require PathReal.
Require PathVirtual.

(** Abbreviations. *)
Module E := Error.
Open Scope list_scope.

(** An archive handler takes the name of an archive and returns an archive
implementation for the name iff there is an archive implementation that can
handle archives of that type. *)
Record t := ArchiveHandler {

  (** Returns [true] iff the handler can handle the type of the archive at [p]. Note
      that this test is purely based on file names. *)
  can_handle : forall (p : PathReal.t), bool;

  (** Load the archive at [p] using mount point [m]. *)
  load : forall (p : PathReal.t) (m : PathVirtual.t), FilesystemOp.t Archive.t;

  (** The [load] function always sets the correct mount point. *)
  load_path_correct : forall (p : PathReal.t) (m : PathVirtual.t) (r : Archive.t),
    load p m = E.Success r -> (Archive.mount_path r) = m
}.

(** The list of known archive handlers is immutable. *)
Parameter handlers : list t.

(** Given a list of archive handlers, the first handler that can handle an
archive is one that is used to load the archive. *)
Fixpoint handle
  (handlers : list t)
  (p        : PathReal.t)
  (m        : PathVirtual.t)
: FilesystemOp.t Archive.t :=
  match handlers with
  | nil     => Error.Failure FilesystemOp.Error_Unsupported_Archive
  | h :: hs =>
    if (can_handle h) p
    then (load h) p m
    else handle hs p m
  end.

