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
(** Names of files and directories. *)
Require Coq.Strings.String.
Require Coq.Logic.ProofIrrelevance.
Require StringAux.

Open Scope string_scope.

(** Names in [jvvfs] are specifically not allowed to contain:
- Forward slashes (['/'], ASCII [0x2f]), as this is used as a path separator on UNIX and in [jvvfs] virtual paths.
- Backslashes (['\'], ASCII [0x5c]), as this is used as a path separator on Microsoft Windows.
- A series of two or more dots (['.'], ASCII [0x2e]), as this is a reserved name on UNIX-like platforms.
- Colons ([':'], ASCII [0x3a]), as these are used to identify "drives" on some operating systems.
- Null (ASCII [0x0]), as almost no operating systems permit these in file names.
*)

Definition slash     := "/".
Definition backslash := "\".
Definition dots      := "..".
Definition colon     := ":".
Definition null      := String.String (Ascii.ascii_of_nat 0) String.EmptyString.

(** Therefore, a [string] is a valid [name] if it does not contain any of the
    above character sequences. *)
Definition valid_name (s : String.string) : Prop :=
  (~StringAux.contains s slash)  /\
  (~StringAux.contains s backslash) /\
  (~StringAux.contains s dots) /\
  (~StringAux.contains s colon) /\
  (~StringAux.contains s null).

(** A name is a [string] and a proof that it is a valid name. *)
Definition t := { s : String.string | valid_name s }.

(** Equality of [names] is decidable. *)
Theorem eq_decidable : forall (x y : t),
  {x = y}+{~x = y}.
Proof.
  destruct x as [s0 s0p].
  destruct y as [s1 s1p].
  destruct (String.string_dec s0 s1) as [H_s0s1_eq|H_s0s1_neq].
    left.  subst; f_equal; apply ProofIrrelevance.proof_irrelevance.
    right. inversion 1; contradiction.
Qed.

(** A tactic for producing validity proofs from valid string constants. *)
Ltac valid_name_compute :=
  repeat match goal with
  | [ |- valid_name _]                                => split
  | [ |- ~StringAux.contains _ _ /\ _ ]               => split
  | [ |- ~StringAux.contains _ _ ]                    => vm_compute; intuition
  | [ H  : Ascii.Ascii _ _ _ _ _ _ _ _ = _ |- False ] => inversion H
  end.

(** Some example valid names include [bin], [usr], [file.txt], and [ps]. *)
Example bin : t.
Proof.
  apply (exist _ "bin").
  valid_name_compute.
Qed.

Example usr : t.
Proof.
  apply (exist _ "usr").
  valid_name_compute.
Qed.

Example file_txt : t.
Proof.
  apply (exist _ "file.txt").
  valid_name_compute; inversion H.
Qed.

Example ps : t.
Proof.
  apply (exist _ "ps").
  valid_name_compute.
Qed.

(** An example invalid name is "xyz..xyz" *)
Example xyz_invalid : ~valid_name "xyz..xyz".
Proof.
  vm_compute; intuition.
Qed.
