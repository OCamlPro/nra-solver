(lang dune 3.17)
(name nra_solver)
(using ctypes 0.3)

(authors "Alt-Ergo developers <alt-ergo@ocamlpro.com>")
(maintainers "Alt-Ergo developers <alt-ergo@ocamlpro.com>")
(homepage "https://alt-ergo.ocamlpro.com/")
(documentation "https://ocamlpro.github.io/alt-ergo")
(bug_reports "https://github.com/OCamlPro/alt-ergo/issues")
(license "LicenseRef-Proprietary")

(generate_opam_files true)

; If you add new (package) entries you need to update the DUNE_PACKAGES
; variable in the Makefile.

(package
  (name nra_solver)
  (synopsis "NRA template")

  ; Note: if you change or add depencies, you need to call `make setup` for
  ; dependencies to be installed.
  (depends
    ocaml
    dolmen
    dolmen_loop
    zarith
    (flint (>= 0.4))
    libpoly_bindings
    topkg
    cmdliner
    (qcheck :with-test)
    (odoc :with-doc)
    (utop :dev) 
    (down :dev)
    (ocaml-lsp-server :dev)
    (ocamlformat (and (= 0.27.0) :dev))))
