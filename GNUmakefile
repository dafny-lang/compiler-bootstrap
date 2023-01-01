# User configuration
# ==================

# Where to find the main Dafny repository.
DAFNY_ROOT ?= ../..
DAFNY_ROOT := $(realpath $(DAFNY_ROOT))
dafny_Source := $(DAFNY_ROOT)/Source
export DAFNY_ROOT

# Additional flags for `dotnet run`
DAFNY_DOTNET_RUN_FLAGS ?=

# Sanity checks
# =============

# Repo setup
ifeq ($(realpath $(dafny_Source)),)
define error_message
Error: Dafny source directory not found at $(dafny_Source).

This repository needs access to a clone of the main Dafny repository to build.
The easiest way to set this up is to clone the `compiler-bootstrap` branch of
the main repository, which includes a copy of this repo as a submodule in its
`Source/Bootstrap/` folder.  Alternatively, you can set the path to the root of
a Dafny clone when invoking `make` with `make DAFNY_ROOT=path/to/dafny/clone/`.
endef

$(error $(error_message))
endif

# Make configuration
# ==================

default: build

MAKEFLAGS += --no-builtin-rules
.SUFFIXES:
FORCE:

# External dependencies
# =====================

# Where to find various dependencies from Dafny's sources
AutoExtern = $(dafny_Source)/AutoExtern
DafnyDriver = $(dafny_Source)/DafnyDriver/DafnyDriver
DafnyCore = $(dafny_Source)/DafnyCore/DafnyCore
DafnyASTRoot = $(dafny_Source)/DafnyCore/AST
DafnyAST = $(wildcard $(DafnyASTRoot)/*.cs $(DafnyASTRoot)/Expressions/*.cs $(DafnyASTRoot)/Statements/*.cs)
DafnyRuntime := $(dafny_Source)/DafnyRuntime/DafnyRuntime.cs

DAFNY ?= dotnet run --project $(DafnyDriver).csproj $(DAFNY_DOTNET_RUN_FLAGS) --
dafny_codegen := $(DAFNY) -spillTargetCode:3 -compile:0 -noVerify -useRuntimeLib
dafny_typecheck := $(DAFNY) -dafnyVerify:0
dafny_verify := $(DAFNY) -compile:0  -trace -verifyAllModules -showSnippets:1 -vcsCores:8

# Project files
# =============

# Subprojects
csharp := src/Backends/CSharp
repl := src/REPL
validator := src/Tools/Validator
auditor := src/Tools/Auditor

# Binaries
csharp_dll := $(csharp)/publish/CSharpCompiler.dll
repl_dll := $(repl)/publish/REPL.dll
validator_dll := $(validator)/publish/Validator.dll
auditor_dll := $(auditor)/publish/DafnyAuditor.dll
dlls := $(csharp_dll) $(repl_dll) $(auditor_dll) $(validator_dll)
publish_dirs := $(csharp)/publish $(repl)/publish $(validator)/publish $(auditor)/publish

# Entry points
dfy_entry_points := $(repl)/Repl.dfy $(csharp)/Compiler.dfy $(auditor)/Auditor.dfy $(validator)/Validator.dfy
cs_entry_points := $(dfy_entry_points:.dfy=.cs)
cs_roots := $(dir $(cs_entry_points))
cs_objs := $(cs_roots:=bin) $(cs_roots:=obj)

# Model files (contain traits that give type signatures of existing C# and Dafny/Boogie classes)
interop := src/Interop
csharp_model := $(interop)/CSharpModel.dfy
dafny_model := $(interop)/CSharpDafnyModel.dfy
dfy_models := $(csharp_model) $(dafny_model)

# Interop files (contain Dafny functions implemented in C# that help interop with the models)
dfy_interop := $(interop)/CSharpInterop.dfy $(interop)/CSharpDafnyInterop.dfy $(interop)/CSharpDafnyASTInterop.dfy
cs_interop := $(dfy_interop:.dfy=.cs)

# Test files (regular Dafny files compiled to C#)
dfy_tests := $(wildcard test/*.dfy)
cs_tests := $(dfy_tests:.dfy=.cs)

# Rules
# =====

# Auto-generate a model of DafnyAST.cs
$(dafny_model): $(DafnyCore).csproj $(DafnyAST) $(dafny_model).template $(AutoExtern)/Program.cs
	dotnet run --project $(AutoExtern)/AutoExtern.csproj -- \
		$(DafnyCore).csproj "Microsoft.Dafny" "$(dafny_model).template" "" "$@" \
		--rewrite "Microsoft.Boogie:Boogie" \
		--skip-interface "Microsoft.Dafny.ICloneable" \
		$(DafnyAST)

# Copy basic C# model into current directory (to make it easier to refer to it from Dafny)
$(csharp_model): $(AutoExtern)/CSharpModel.dfy
	cp "$<" "$@"

# Translate the compiler from Dafny to C#
$(csharp)/Compiler.cs: $(csharp)/Compiler.dfy $(dfy_models) $(dfy_interop) $(DafnyRuntime)
	$(dafny_codegen) $<

$(validator)/Validator.cs: $(validator)/Validator.dfy $(dfy_models) $(dfy_interop) $(DafnyRuntime)
	$(dafny_codegen) $<

$(auditor)/Auditor.cs: $(auditor)/Auditor.dfy $(dfy_models) $(dfy_interop) $(DafnyRuntime)
	$(dafny_codegen) $<

# Compile the resulting C# code
$(csharp_dll): $(csharp)/Compiler.cs $(cs_interop)
	dotnet publish -o $(csharp)/publish $(csharp)/CSharpCompiler.csproj

$(validator_dll): $(validator)/Validator.cs $(validator)/EntryPoint.cs $(cs_interop)
	dotnet publish -o $(validator)/publish $(validator)/Validator.csproj

$(auditor_dll): $(auditor)/Auditor.cs $(auditor)/EntryPoint.cs $(cs_interop)
	dotnet publish -o $(auditor)/publish $(auditor)/DafnyAuditor.csproj

# Run it on tests
test/%.cs: test/%.dfy $(csharp_dll) $(DafnyRuntime)
	$(dafny_codegen) -plugin:$(csharp_dll) -compileTarget:cs "$<"

%.v: %.dfy $(validator_dll)
	$(dafny_typecheck) -plugin:$(validator_dll) "$<" | \
		sed -E -e 's/(.*)[(]([-0-9]+), *([-0-9]+)[)]:/\1:\2:\3:/g'

# Compile the REPL
# DISCUSS: Dependency tracking in Dafny
$(repl)/Repl.cs: $(repl)/Repl.dfy $(dafny_model) $(dfy_models) $(dfy_interop) $(DafnyRuntime)
	$(dafny_codegen) "$<"
	sed -i.bak -e 's/__AUTOGEN__//g' "$@"
	rm "$@.bak"

$(repl_dll): $(repl)/Repl.cs $(repl)/REPLInterop.cs $(cs_interop)
	dotnet publish -o $(repl)/publish --configuration=Release $(repl)/REPL.csproj

# Entry points
# ============

tests: $(cs_tests)

repl: $(repl_dll) FORCE
	dotnet exec $<

validator: $(validator_dll) FORCE

auditor: $(auditor_dll) FORCE

typecheck: $(dfy_models)
	$(dafny_typecheck) $(dfy_entry_points)

verify: $(dfy_models)
	$(dafny_verify) $(dfy_entry_points)

build: $(dlls)

clean:
	rm -fr $(cs_entry_points) $(dafny_model) $(cs_objs) $(publish_dirs)
