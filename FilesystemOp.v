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
(** Filesystem operations that can fail and return an error code. *)
Require Error.

(** The possible error codes raised by I/O operations. *)
Inductive error_code :=

  (** Raised on arbitrary I/O errors (usually raised by the operating system on hardware faults). *)
  | Error_IO

  (** Raised upon trying to execute an operation that only applies to files on a directory. *)
  | Error_Is_A_Directory

  (** Raised upon trying to obtain a reference to a nonexistent filesystem object. *)
  | Error_Nonexistent

  (** Raised upon trying to execute an operation that only applies to directories on a file. *)
  | Error_Not_A_Directory

  (** Raised upon trying to load an archive of an unsupported format. *)
  | Error_Unsupported_Archive.

(** The type [t] represents a computation that can perform arbitrary I/O
when executed, and will raise one of the [error_code] values on failure. *)
Definition t (S : Type) :=
  Error.t error_code S.
