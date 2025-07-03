#!/bin/bash
find ./test/unsat -name "*.smt2" -print0 | while IFS= read -r -d $'\0' fl; do echo "Traitement du fichier UNSAT : $fl"   ;   dune exec -- bin/frontend.exe "$fl"; done