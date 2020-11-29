# Baby-Modelica 3.4.0 (2020-01-29)

Copyright (C) 2018-2020 RIKEN R-CCS

__Baby-Modelica comes with ABSOLUTELY NO WARRANTY.__

Baby-Modelica is a simple parser of the Modelica language
specification 3.4.  Its intended use is to create data extraction
tools for Modelica models.  The parser can dump a flat model.  A
generated flat model is to be reloadable by Modelica compliers.
Current status is a pre-zero version, we are working towards version
zero.  The version number of Baby-Modelica is the last digits,
appended to the version number of the Modelica language specification.

Baby-Modelica is written in SML'97 (Standard ML) and developed mainly
with Poly/ML (on SUNOS 5.11/amd64) and tested with SML/NJ.  It uses a
modified BYACC parser generator (not ml-yacc), which needs be obtained
separately.

See [https://www.modelica.org](https://www.modelica.org) for
information of Modelica.

If someone might be unfamiliar with SML, see
[http://sml-family.org](http://sml-family.org).  Poly/ML is at
[https://www.polyml.org](https://www.polyml.org) and SML/NJ is at
[https://smlnj.org](https://smlnj.org).

----

## Source code files and directories

See frontend/notes.pdf first, then start with frontend/bbm.sml.
* [frontend/notes.pdf](frontend/notes.pdf): random implementation notes
* frontend/bbm.sml: a list of the source code files

The toplevel directories are as follows.
* [frontend](frontend): the source code
* [silly-models](silly-models): trivial code to check the specification
* [code-examples](code-examples): code snippets from the specification

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
postbinder.xbind () ;
postbinder.xreplace () ;
flatdumper.xdump () ;
valOf (classtree.xfetch1 "tank") ;
valOf (classtree.xfetch1 "wall.G") ;
valOf (classtree.xfetch1 "") ;
valOf (classtree.xfetch1 ".Modelica") ;
......
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
