#!/bin/sh

coq_compile()
{
  echo "coqc: $1" 1>&2
  coqc -opt "$1"
  if [ $? -ne 0 ]
  then
    exit 1
  fi
}

grep -n 'Admitted' *.v
case $? in
  0) echo "warning: Some Admissions remain" 1>&2 ;;
  1) ;; 
  *) exit 1
esac

grep -n 'admit' *.v
case $? in
  0) echo "warning: Some proofs completed with 'admit'" 1>&2 ;;
  1) ;; 
  *) exit 1
esac

coq_compile ListAux.v
coq_compile StringAux.v
coq_compile MapWeak.v
coq_compile MapWeakAux.v
coq_compile SetWeak.v
coq_compile NonEmptyStack.v
coq_compile Stack.v
coq_compile ListMapWeak.v
coq_compile ListNonEmptyStack.v
coq_compile ListSetWeak.v
coq_compile ListStack.v
coq_compile Error.v

coq_compile Size.v
coq_compile Time.v
coq_compile Names.v
coq_compile PathVirtual.v
coq_compile PathReal.v
coq_compile FilesystemRef.v
coq_compile FilesystemOp.v
coq_compile InputStream.v
coq_compile Archive.v
coq_compile ArchiveHandler.v
coq_compile Filesystem.v

ocamllex coq2html.mll                     || exit 1
ocamlopt -o coq2html str.cmxa coq2html.ml || exit 1

rm -rf doc                            || exit 1
mkdir doc                             || exit 1
./coq2html -o 'doc/%.html' *.glob *.v || exit 1
cp *.css      doc                     || exit 1
cp *.js       doc                     || exit 1
cp *.v        doc                     || exit 1
cp index.html doc                     || exit 1

