================
 Dafny in Dafny
================

A work-in-progress reimplementation of Dafny's compilers, in Dafny.

Trying it out
=============

Clone this repository as part of the ``compiler-bootstrap`` branch of the main Dafny repository, then use ``make tests`` or ``make repl`` (and read through the `Makefile <./GNUmakefile>`__ to see all the steps).  Alternatively, if you cloned this repo on its own, ``make`` will complain and ask you how to select which Dafny to run for bootstrapping.

Overview
========

- First we generate definitions to model the existing |DafnyAst.cs|_ in Dafny.  The result is ``src/Interop/CSharpDafnyASTModel.dfy``.

- Then we write a compiler in Dafny against this interface in |Compiler.dfy|_.

- Then we compile that to C# using the existing compiler, and link it with a `wrapper <./src/Backends/CSharp/EntryPoint.cs>`__ to get a Dafny compiler plugin.

Supported language
------------------

Our initial target is the purely functional subset of Dafny (aka non-ghost functions).  This is also the subset that the compiler is written on (our first large application will be bootstrapping the compiler itself).
The Dafny-in-Dafny AST is defined in ``src/AST.dfy``.  We have operational semantics for most of it in ``src/Semantics/Interp.dfy``.  The C# backend is in ``src/Backends/CSharp/Compiler.dfy``, but it is not up-to-date (we are focusing on the language and the semantics).

Tools
-----

The Dafny in Dafny code base supports two key executable programs:

* A REPL, for interactively evaluating Dafny statements, in ``src/REPL``.

* An auditor plugin, for reporting assumptions in a Dafny program, in ``src/Tools/Auditor``.

Design notes
------------

For details on how we interop with the existing C# codebase, read through https://github.com/dafny-lang/dafny/pull/1769.

Project hierarchy
=================

``src/``
  ``AST/``
    ``Syntax.dfy``
      Dafny expressions and statements
    ``Entities.dfy`` (TODO)
      Dafny classes, modules, methods, and functions
    ``Translator.dfy``
      Translation from ``DafnyAST.cs`` to our own AST and entities
    ``Predicates.dfy``
      Predicates on expressions
  ``Semantics/``
    ``Values.dfy``
      Dafny runtime values
    ``Printer.dfy``
      Converter from values to strings
    ``Interp.dfy``
      Operational semantics for the pure subset of Dafny
    ``Equiv.dfy``
      Definition of program equivalence based on ``Interp.dfy``
  ``Transforms/``
    ``Generic.dfy``
      Basic definitions for AST transformers
    ``BottomUp.dfy``
      Bottom-up rewriter
  ``Passes/``
    ``Pass.dfy``
      Definition of a compiler pass
    ``EliminateNegatedBinops.dfy``
      Simple demo pass
  ``REPL/``
    ``Repl.dfy``
      Driver for a REPL build on top of ``Interp/``
    ``REPLInterop.cs``
      Helper functions for ``Repl.dfy``
  ``Backends/``
    ``CSharp/``
      ``Compiler.dfy``
        C# compiler
      ``EntryPoint.cs``
        C# wrapper around ``Compiler.dfy``
  ``Interop/``
    ``CSharpDafnyASTInterop.dfy``
      Extern declarations for functions that deal with Dafny AST nodes and cannot be implemented in pure Dafny
    ``CSharpDafnyASTInterop.cs``
      Implementations for ``CSharpDafnyASTInterop.dfy``
    ``CSharpDafnyInterop.dfy``
      Extern declarations for functions that deal with Dafny types and cannot be implemented in pure Dafny
    ``CSharpDafnyInterop.cs``
      Implementations for ``CSharpDafnyInterop.dfy``
    ``CSharpInterop.dfy``
      Extern declarations for functions that deal with C# types and cannot be implemented in pure Dafny
    ``CSharpInterop.cs``
      Implementations for ``CSharpInterop.dfy``
    ``CSharpDafnyASTModel.dfy.template``
      Template used by ``AutoExtern`` to generate a Dafny model from ``DafnyAST.cs``
    ``CSharpDafnyModel.dfy``
      Extern declarations for existing C# functions from Dafny's codebase
    ``CSharpModel.dfy``
      Extern declarations for C#'s standard library (automatically copied from ``AutoExtern``)
  ``Tools/``
    ``Auditor/``
      ``Auditor.dfy``
        An auditor to identify assumptions in a Dafny program.
      ``EntryPoint.cs``
        The C# entry point that enables the auditor to be used as a plugin from Dafny.
      ``Report.dfy``
        The ``Report`` data structure used by the auditor.
  ``Utils/``
    ``Library.dfy``
      Utility functions (should move to shared library)
    ``StrTree.dfy``
      Tree of strings (for efficient concatenation).
``GNUmakefile``
  Build configuration

.. |Compiler.dfy| replace:: ``src/Backends/CSharp/Compiler.dfy``
.. _Compiler.dfy: ./src/Backends/CSharp/Compiler.dfy

.. |DafnyAst.cs| replace:: ``DafnyAst.cs``
.. _DafnyAst.cs: https://github.com/dafny-lang/dafny/blob/dind/Source/Dafny/AST/DafnyAst.cs 
