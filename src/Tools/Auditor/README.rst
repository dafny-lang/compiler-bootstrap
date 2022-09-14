=============
Dafny Auditor
=============

A tool to audit Dafny programs and report on assumptions contained
within.

Overview
========

It currently detects the following forms of assumption:

* Anything marked with the ``{:axiom}`` attribute.

* Declarations with at least one ``ensures`` clauses that

  * lack a body, or

  * are marked with the ``{:extern}`` attribute.

* Explicit ``assume`` statements.

In the future, it will detect additional constructs that introduce
assumptions and integrate the results of other analyses.

Building
========

From the top level of this repository, run the following.

.. code-block:: shell

  git clone https://github.com/dafny-lang/dafny
  (cd dafny && git checkout compiler-bootstrap)
  DAFNY_ROOT=dafny make auditor

Usage
=====

From the top level of this repository, run the following.

.. code-block:: shell

  ./dafny/Scripts/dafny /plugin:src/Tools/Auditor/bin/Debug/net6.0/DafnyAuditor.dll,<output file> /compile:0 /noVerify <input files>

Here, ``<input files>`` should be one or more Dafny source files, and
``<output file>`` indicates where to write the report. The
