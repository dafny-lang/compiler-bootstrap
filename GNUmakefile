# User configuration
# ==================

# Where to find the main Dafny repository.
DAFNY_ROOT ?= ../..
DAFNY_ROOT := $(realpath $(DAFNY_ROOT))
dafny_Source := $(DAFNY_ROOT)/Source
export DAFNY_ROOT

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
DafnyPipeline = $(dafny_Source)/Dafny/DafnyPipeline
DafnyAST = $(dafny_Source)/Dafny/AST/DafnyAst
DafnyRuntime := $(dafny_Source)/DafnyRuntime/DafnyRuntime.cs

dafny := dotnet run --project $(DafnyDriver).csproj --
dafny_codegen := $(dafny) -spillTargetCode:3 -compile:0 -noVerify
dafny_typecheck := $(dafny) -dafnyVerify:0
dafny_verify := $(dafny) -compile:0  -trace -verifyAllModules -showSnippets:1 -vcsCores:8

# Project files
# =============

# Subprojects
csharp := src/CSharp
repl := src/REPL

# Binaries
plugin_dll := $(csharp)/bin/Debug/net6.0/CSharpCompiler.dll
repl_dll := $(repl)/bin/Release/net6.0/Repl.dll
dlls := $(plugin_dll) $(repl_dll)

# Entry points
dfy_entry_points := $(repl)/Repl.dfy $(csharp)/Compiler.dfy
cs_entry_points := $(dfy_entry_points:.dfy=.cs)

# Model files (contain traits that give type signatures of existing C# and Dafny/Boogie classes)
csharp_model := src/CSharpModel.dfy
ast_model := src/CSharpDafnyASTModel.dfy
dfy_models := $(csharp_model) src/CSharpDafnyModel.dfy $(ast_model)

# Interop files (contain Dafny functions implemented in C# that help interop with the models)
dfy_interop := src/CSharpInterop.dfy src/CSharpDafnyInterop.dfy src/CSharpDafnyASTInterop.dfy
cs_interop := $(dfy_interop:.dfy=.cs)

# Test files (regular Dafny files compiled to C#)
dfy_tests := $(wildcard test/*.dfy)
cs_tests := $(dfy_tests:.dfy=.cs)

# Rules
# =====

# Auto-generate a model of DafnyAST.cs
$(ast_model): $(DafnyPipeline).csproj $(DafnyAST).cs $(ast_model).template $(AutoExtern)/Program.cs
	dotnet run --project $(AutoExtern)/AutoExtern.csproj -- \
		$(DafnyPipeline).csproj $(DafnyAST).cs "Microsoft.Dafny" "$(ast_model).template" \
		"" "$@"

# Copy basic C# model into current directory (to make it easier to refer to it from Dafny)
$(csharp_model): $(AutoExtern)/CSharpModel.dfy
	cp "$<" "$@"

# Translate the compiler from Dafny to C#
$(csharp)/Compiler.cs: $(csharp)/Compiler.dfy $(dfy_models) $(dfy_interop) $(DafnyRuntime)
	$(dafny_codegen) $<
	sed -i.bak -e 's/__AUTOGEN__//g' "$@"
	rm "$@.bak" # https://stackoverflow.com/questions/4247068/

# Compile the resulting C# code
$(plugin_dll): $(csharp)/Compiler.cs $(cs_interop)
	dotnet build $(csharp)/CSharpCompiler.csproj

# Run it on tests
test/%.cs: test/%.dfy $(plugin_dll) $(DafnyRuntime)
	$(dafny_codegen) -plugin:$(plugin_dll) -compileTarget:cs "$<"

# Compile the REPL
# DISCUSS: Dependency tracking in Dafny
$(repl)/Repl.cs: $(repl)/Repl.dfy $(ast_model) $(dfy_models) $(dfy_interop) $(DafnyRuntime)
	$(dafny_codegen) "$<"
	sed -i.bak -e 's/__AUTOGEN__//g' "$@"
	rm "$@.bak"

$(repl_dll): $(repl)/Repl.cs $(repl)/ReplInterop.cs $(cs_interop)
	dotnet build --configuration=Release $(repl)/REPL.csproj

# Entry points
# ============

tests: $(cs_tests)

repl: $(repl_dll) FORCE
	dotnet exec $<

typecheck:
	$(dafny_typecheck) $(dfy_entry_points)

verify:
	$(dafny_verify) $(dfy_entry_points)

build: $(dlls)

clean:
	rm -f $(cs_entry_points) $(ast_model)
