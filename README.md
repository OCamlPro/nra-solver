# NRA Solver Internship Project

Welcome! We're excited to have you on board. This document will guide you
through setting up the project environment and understanding the initial
codebase for the Non-linear Real Arithmetic (NRA) solver you'll be working on.

The goal of this internship is to implement an NRA solver in OCaml. We have
provided a basic project structure, a template library interface (`.mli`), a
stub implementation (`.ml`), and a frontend application that can parse SMT-LIB
v2 files for testing.

## Prerequisites

Before you begin, please ensure you have the following installed:

1.  **OCaml:** The programming language used for this project.
2.  **opam:** The OCaml package manager. It's used to install project
    dependencies and manage OCaml compiler versions.

If you don't have them installed, follow the instructions on the official OCaml
website: [https://ocaml.org/install](https://ocaml.org/install).

**Make sure to allow opam to setup shell hooks to automatically activate the
project environment!**

## Project Setup

The project uses `dune` as its build system and `opam` for managing dependencies
within a local switch (a self-contained environment for this project). The
provided `Makefile` simplifies the setup process.

1.  **Clone the Repository:** Get the project code onto your local machine.

    ```bash
    git clone git@gitlab.ocamlpro.com:alt-ergo-team-at-ocp/template-stage-nra.git
    cd template-stage-nra
    ```

2.  **Install Dependencies:** Run the following command in the project's root
    directory. This will:

    - Create a local `opam` switch in the `_opam/` directory if it doesn't exist
      (this isolates project dependencies from your global OCaml installation).
    - Ensure the `.opam` package definition file is up-to-date based on
      `dune-project`.
    - Install all required OCaml packages listed in the `dune-project` file into
      the local switch.

    ```bash
    make setup
    ```

    This might take a few minutes the first time.

3.  **(Optional) Install Development Tools:** For a better development experience
    (editor support, interactive top-level), you can install some extra tools:
    ```bash
    make dev-setup
    ```
    This installs `utop` (an improved OCaml REPL), `ocaml-lsp-server` (for
    editor integration), `ocamlformat` (code formatter), and `down` (improvement
    to the default OCaml REPL).

4.  **(Optional) Install new dependencies:** You might need extra dependencies.
    Add them in `dune-project` and update your environment:
    ```bash
    make setup
    ```

## Building the Project

The project uses `dune` for building. The `Makefile` provides convenient
shortcuts, feel free to look at how they are implemented and call `dune`
yourself:

- **Build:** Compile the library and the executable.

  ```bash
  make build
  ```

- **Watch Mode:** Automatically rebuild the project when source files change. This is useful during development.

  ```bash
  make watch
  ```

- **Clean:** Remove build artifacts.
  ```bash
  make clean
  ```

- **Top level:** Launch the toplevel utop with your project and all its
  dependencies loaded. This is useful for quick testing.
  ```bash
  make utop
  ```

## Running the Frontend

A frontend executable (`nra_solver.exe`) is provided in `bin/` to test the
solver library. It uses the [Dolmen](https://github.com/Gbury/dolmen) library to
parse input files written in the SMT-LIB v2 format, specifically targeting the
`QF_NRA` logic (Quantifier-Free Non-linear Real Arithmetic).

You can run the frontend on an SMT-LIB file like this:

```bash
# Using dune exec (recommended as it ensures the correct environment)
dune exec -- ./bin/frontend.exe test/example.smt2
```

Currently, since the solver logic in `lib/nra_solver.ml` is just a stub, the
frontend will always output:

```
unknown
```

Your goal will be to implement the solver so that it correctly outputs `sat` or
`unsat` for solvable/unsolvable problems.

## Project Structure

```
.
├── Makefile            # Build/Setup shortcuts
├── README.md           # This file
├── bin/                # Source for the executable frontend
│   └── frontend.ml     # Parses SMT-LIB and calls the solver library
├── dune-project        # Dune project configuration (metadata, dependencies)
├── lib/                # Source for the NRA solver library
│   ├── dune            # Dune build rules for the library
│   ├── nra_solver.ml   # Stub implementation of the solver (Your main focus)
│   └── nra_solver.mli  # Interface definition for the solver
├── nra_solver.opam     # Auto-generated opam package file
└── test/               # (Optional) Place for unit tests later
```

- **`lib/`:** Contains the core solver library.
  - `nra_solver.mli`: This is the OCaml _interface_ file. It defines the types
    (`t`, `variable`, `term`, etc.) and functions that your solver _must_
    provide. Study this file carefully to understand the required API.
  - `nra_solver.ml`: This is the OCaml _implementation_ file. Currently, it
    contains minimal stub code that matches the interface (`.mli`) but doesn't
    perform any real solving logic. **This is where you will implement the NRA
    solving algorithm.**
- **`bin/`:** Contains the frontend application.
  - `frontend.ml`: This code uses the `Dolmen` library to parse SMT-LIB input.
    It translates SMT-LIB commands like `(declare-const x Real)`, `(assert (= x
1.0))`, `(assert (> (* x y) 0.0))`, and `(check-sat)` into calls to the
    functions defined in `lib/nra_solver.mli` (e.g.,
    `Nra_solver.create_variable`, `Nra_solver.assert_eq`, `Nra_solver.solve`).
    You generally won't need to modify this file much, but understanding how it
    uses your library is crucial for testing.
- **`dune-project`:** Defines project metadata, OCaml version constraints, and
  dependencies.
- **`Makefile`:** Simplifies common tasks like setup, building, and cleaning.

## Your Task

Your primary goal is to implement the Non-linear Real Arithmetic (NRA) decision
procedure described in the following research paper:

**[Deciding the Consistency of Non-Linear Real Arithmetic Constraints with a
Conflict Driven Search Using Cylindrical Algebraic
Coverings](https://arxiv.org/pdf/2003.05633)**

**Initial Focus: Coverings**

As a first step to familiarize yourself with the codebase and testing setup, you
will focus on implementing a data structure for representing **coverings** of
the real line. This will involve:

1. **Defining the `covering` type:** Determine how to represent coverings in
   `lib/nra_solver.mli` and `lib/nra_solver.ml`. See the paper for what
   informations are expected in coverings, and discuss your options with the
   team before making a decision!
2. **Implementing `is_covering`:** Write a function that checks if a given
   `covering` value is structurally valid according to your definition. Ideally,
   your functions for _creating_ coverings should make it impossible to create one
   where `is_covering` is false (i.e., validity is maintained by construction).
   This function helps document and verify these invariants.
3. **Implementing `is_good_covering`:** Define and implement a check for
   _additional_ properties that make a "good" covering, as defined in the
   paper.
4. **Implementing `compute_good_covering`:** Write a function that takes any
   valid covering and transforms it into an equivalent "good" covering.
5. **Writing QCheck Generators and Properties:** Update `test/test_nra.ml` with
   appropriate generators for your `covering` type and add/refine properties to
   test your implementation thoroughly using `make test`.

**Overall Goal**

After establishing the covering infrastructure, you will move on to the main
solver implementation:


6. **Define Internal State:** Replace the placeholder types (like `type t =
unit`, `type term = unit`) with concrete data structures suitable for
   representing variables, terms, constraints, and the overall solver state.
7. **Implement Term Construction:** Flesh out the functions within the `Term`
   module (`variable`, `real`, `add`, `mul`, etc.) to build an internal
   representation of NRA terms.
8. **Implement Assertions:** Implement the `assert_eq`, `assert_leq`, etc.,
   functions to store the constraints provided by the input problem within the
   solver's state (`t`).
9. **Implement the Solver:** Implement the core `solve` function following the
   paper.
   - `Sat`: If the constraints are satisfiable.
   - `Unsat`: If the constraints are unsatisfiable.
   - `Unknown`: If the solver times out or cannot determine satisfiability
     (once the solver is complete, this should not happen for `QF_NRA`!).

## Key Libraries and Concepts

- **OCaml:** [https://ocaml.org/learn/](https://ocaml.org/learn/) - The language
  itself. Focus on modules, types, pattern matching, and functional programming
  concepts.
- **Dune:** [https://dune.build/](https://dune.build/) - The build system. You
  mostly interact with it via `make` or simple `dune build` commands.
- **Dolmen:** [https://github.com/Gbury/dolmen](https://github.com/Gbury/dolmen)
  Used by the frontend (`bin/frontend.ml`) to parse SMT-LIB. You don't need to
  be an expert, but knowing its role helps understand how input files are
  processed.
- **SMT-LIB:** [http://smtlib.cs.uiowa.edu/](http://smtlib.cs.uiowa.edu/) - The
  standard format for SMT solver input. Familiarize yourself with the basic syntax
  for the `QF_NRA` logic.
- **NRA (Non-linear Real Arithmetic):** The theory your solver needs to handle.
  This involves equations and inequalities over real variables with polynomial
  terms (including multiplication). Research common decision procedures for NRA.
- **Zarith & Flint:** These libraries (listed as dependencies) provide
  arbitrary-precision arithmetic for integers (`Zarith`) and
  rationals/floating-point (`Flint`). They will likely be essential for handling
  real number representations accurately within your solver, although the current
  stub doesn't use them yet.
  - Zarith: [https://github.com/ocaml/Zarith](https://github.com/ocaml/Zarith)
  - Flint:
    [https://github.com/bobot/ocaml-flint](https://github.com/bobot/ocaml-flint)
    (Note: ocaml-flint wraps the Flint C library:
    [https://flintlib.org/](https://flintlib.org/))

## Getting Started & Asking Questions

1.  Start by studying the `lib/nra_solver.mli` interface file thoroughly.
2.  Think about how you would represent NRA terms and constraints internally in
    `lib/nra_solver.ml`.
3.  Begin implementing the `Term` module functions and the assertion functions to
    store constraints.
4.  Research NRA decision procedures to inform your implementation of the `solve`
    function.

Don't hesitate to ask questions! Reach out to Pierrot or Basile if you get stuck,
need clarification, or want to discuss design choices.

Good luck!
