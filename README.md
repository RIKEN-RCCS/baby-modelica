# Baby-Modelica 3.4.0 (2021-03-18)

Copyright (C) 2018-2021 RIKEN R-CCS

__Baby-Modelica comes with ABSOLUTELY NO WARRANTY.__

Baby-Modelica is a simple frontend (parser+flattener) for the Modelica
language specification 3.4.  It parses a source code then performs
simple syntactic transformations, and optionally dumps a flat model.
Flattening is indispensable even for simple tools, because taking
parameter values is not direct as they may be substituted multiple
times by nested parameterization.  Flattening is a major part of
Modelica, and it resolves all the features as an object-oriented
language.  A generated flat model is hopefully to be re-readable by
Modelica compilers.

Current status is a pre-zero version, and we are working towards
version zero.  The version number of Baby-Modelica is the last digits,
appended to the version number of the Modelica language specification.

Baby-Modelica is written in SML'97 (Standard ML) and developed mainly
with Poly/ML (on SUNOS 5.11/amd64), but it may work with SML/NJ or
MLton.  It uses a modified BYACC parser generator (not ml-yacc), which
needs be obtained separately.

See [https://www.modelica.org](https://www.modelica.org) for
information of Modelica.

If someone might be unfamiliar with SML, see
[http://sml-family.org](http://sml-family.org).  Poly/ML is at
[https://www.polyml.org](https://www.polyml.org), SML/NJ is at
[https://smlnj.org](https://smlnj.org), and MLton is at
[https://mlton.org](https://mlton.org).

----

## Implementation notes

* [frontend/notes.pdf](frontend/notes.pdf) is implementation notes and
is a kind of a "Modelica reference manual" to supplement the
specification.

## Source code directories

The toplevel directories are as follows.
* [frontend](frontend): the source code
* [silly-models](silly-models): trivial code to check the specification
* [code-examples](code-examples): code snippets from the specification

See [frontend/bbm.sml](frontend/bbm.sml) first as it contains a list
of the source code files.

----

## A simple test run with Poly/ML or SML/NJ

Set the environment variable "MODELICAPATH" to the library paths of
the Modelica Standard Library.  The paths point to the directory
containing such as "Modelica 3.2.3".  Use the MSL-3.2.3 (2019-01-23)
for testing.

Test with the following commands in the "frontend" directory.
"bbm.sml" loads the needed source files.  Flatdumper dumps a flat
model in "x.mo".

```
use "bbm.sml" ;
builder.xreset () ;
builder.xbuild "Modelica.Fluid.Examples.HeatingSystem" ;
connector.xbind () ;
connector.xconnect () ;
flatdumper.xdump () ;
valOf (classtree.xfetch1 "tank") ;
valOf (classtree.xfetch1 "wall.G") ;
valOf (classtree.xfetch1 "") ;
valOf (classtree.xfetch1 ".Modelica") ;
```

## Verbosity settings in PolyML

* Printer setting:
```
PolyML.print_depth (1000) ;
```

* Backtrace setting:
```
PolyML.Compiler.debug := true ;
open PolyML.Debug ;
breakEx Match ;
```

(Reloading files (to recompile) is needed after enabling backtracing).

## Verbosity settings in SML/NJ

* Printer setting:
```
Control.Print.printDepth := 100 ;
Control.Print.printLength := 10000 ;
```

* Backtrace setting:
```
CM.make "$smlnj-tdp/back-trace.cm" ;
SMLofNJ.Internals.TDP.mode := true ;
```

(Reloading files (to recompile) is needed after enabling backtracing).

----

Baby-Modelica is distributed under the BSD 2-Clause License.
