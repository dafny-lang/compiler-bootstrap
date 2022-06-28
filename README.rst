================
 Dafny in Dafny
================

A work-in-progress reimplementation of Dafny's compilers, in Dafny.

Trying it out
=============

Use ``make tests`` or ``make repl`` (and read through the `Makefile <./GNUmakefile>`__ to see all the steps).

Overview
========

- First we generate definitions to model the existing |DafnyAst.cs|_ in Dafny.  The result is ``src/Interop/CSharpDafnyASTModel.dfy``.

- Then we write a compiler in Dafny against this interface in |Compiler.dfy|_.

- Then we compile that to C# using the existing compiler, and link it with a `wrapper <./src/CSharp/EntryPoint.cs>`__ to get a Dafny compiler plugin.

Design notes
============

For details on how we interop with the existing C# codebase, read through https://github.com/dafny-lang/dafny/pull/1769.

Project hierarchy
=================

``src/``
  ``AST/``
    ``Expressions.dfy``
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
    ``Interpreter.dfy``
      Operational semantics for the pure subset of Dafny
  ``Transforms/``
    ``Generic.dfy``
      Basic definitions for AST transformers
    ``BottomUp.dfy``
      Generic bottom-up transformer
  ``Passes/``
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
  ``Utils/``
    ``Library.dfy``
      Utility functions (should move to shared library)
    ``StrTree.dfy``
      Tree of strings (for efficient concatenation).
``GNUmakefile``
  Build configuration

.. |Compiler.dfy| replace:: ``src/CSharp/Compiler.dfy``
.. _Compiler.dfy: ./src/CSharp/Compiler.dfy

.. |DafnyAst.cs| replace:: ``DafnyAst.cs``
.. _DafnyAst.cs: https://github.com/dafny-lang/dafny/blob/dind/Source/Dafny/AST/DafnyAst.cs
