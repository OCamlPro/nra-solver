#!/bin/bash
find ./test/sat -name "*.smt2" -print0 | while IFS= read -r -d $'\0' fl; do echo "Traitement du fichier SAT : $fl"; timeout 5s dune exec -- bin/frontend.exe "$fl"; done
