This archive contains Frama-Clang, a Frama-C plug-in for parsing C++ files,
based on Clang, the C/C++/Objective-C front-end of the LLVM compiler
infrastructure.

# Installation

The following packages must be present on the system in order to compile
Frama-Clang

- llvm and clang (version >= 6.x, preferably 9 or 10)
  - For Ubuntu and Debian, install the following packages:
      libclang-<version>-dev clang-<version>
      (with their dependencies).
  - For Fedora, install the following packages:
      llvm<version>-static clang clang-devel
      (packages such as llvm<version>, llvm<version>-devel and ncurses-devel
       should be included in their dependencies; otherwise, you might need to
       install them as well)
- Frama-C version 21.x Scandium
- OCaml version 4.05 or higher
  (i.e. the same version than the one that was used to compile Frama-C).
- The corresponding camlp5 version

Build the front-end with [autotools](https://en.wikipedia.org/wiki/GNU_Autotools):
```
> git clone https://git.frama-c.com/pub/frama-clang
> cd frama-clang
> export FRAMAC_SHARE=/usr/local/share/frama-c
> autoconf
> ./configure
> make
```

In order to run tests, build frama-c from source:
```
> opam update
> opam install why3
> why3 --version
Why3 platform, version 1.4.0
> why3 config detect
Found prover Alt-Ergo version 2.2.0, OK.
...
> git clone https://git.frama-c.com/pub/frama-c
> cd frama-c
> autoconf
> ./configure
...
configure: wp: partial, gui not enabled
> make install
```

Now reinstall the frama-clang plugin and run the tests like this:
```
> cd frama-clang
> make install
> make tests
```

Depending on the exact configuration of the system, 
the last step might require administrator rights. See `./configure --help`
for possible customization of the configuration stage.

# Usage

Once installed, Frama-Clang will be automatically called by Frama-C's kernel
whenever a C++ source file is encountered. More precisely, files ending 
with `.cpp`, `.C`, `.cxx`, `.c++` or `.cc` will be treated as C++ files.
Files ending with `.ii` will be considered as already pre-processed C++ files.

Options of the plug-in are the following.
- `-cxx-demangling-full` tells Frama-C to display C++ global 
  identifiers with their fully-qualified name (e.g. `::A::x`)
- `-cxx-demangling-short` tells Frama-C to display global 
  C++ identifiers with their unqualified name (e.g. `x`)
- `-cxx-keep-mangling` tells Frama-C to display global C++
  identifiers with the name they have in the C translation (e.g. 
  `_Z1A1x`, that allows to distinguish between overloaded symbols.
  This mangled name is computed from the fully-qualified C++ name
  according to the rules described in the Itanium C++ ABI. Pretty-printing
  the AST with this option should result in compilable C code.
- `-cxx-cstdlib-path <path>` specifies where to look for standard
  C library headers (default is the path to Frama-C's headers)
- `-cxx-c++stdlib-path <path>` specifies where to look for
  standard C++ library headers (default is the path to Frama-Clang headers,
  which are very incomplete)
- `-cxx-nostdinc` do not include in the search paths 
  Frama-C's C/C++ standard headers location (i.e. rely on the system's headers)
- `-cxx-clang-command <cmd>` allows changing the name of the
  command that launches clang and its plugin that outputs the intermediate AST.
  This should only be needed if the front-end as a whole has not been installed
  properly.

In addition, any command-line option taking a function name as
argument (e.g.  `-main`, `-eva-slevel-function`, ...) will accept a
fully qualified C++ name (provided it refers to an existing function
in the code under analysis of course). Note however that it is
currently not possible to distinguish between overloaded functions
using this mechanism.
