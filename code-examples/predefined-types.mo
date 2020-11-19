/* predefined.mo -*-Coding: us-ascii-unix;-*- */

/* 3.6.7 Built-in Variable time */

input Real time (final quantity = "Time", final unit = "s");

/* 4.8 Predefined Types and Classes */

/* In Real, Integer, Boolean, String, and Enumeration, the default to
   "fixed" is true for parameter/constant, and false for other
   variables. */

/* Machine defined types: _BooleanType_ _EnumType_ _IntegerType_
   _RealType_ _StringType_. */

type Real
    _RealType_ value;
    parameter _StringType_ quantity = "";
    parameter _StringType_ unit = "";
    parameter _StringType_ displayUnit = "";
    parameter _RealType_ min = -Inf, max = +Inf;
    parameter _RealType_ start = 0;
    parameter _BooleanType_ fixed;
    parameter _RealType_ nominal;
    parameter _BooleanType_ unbounded = false;
    parameter StateSelect stateSelect = StateSelect.default;
    equation
       assert(value >= min and value <= max, "Variable value out of limit");
end Real;

type Integer
    _IntegerType_ value;
    parameter _StringType_ quantity = "";
    parameter _IntegerType_ min = -Inf, max = +Inf;
    parameter _IntegerType_ start = 0;
    parameter _BooleanType_ fixed;
    equation
       assert(value >= min and value <= max, "Variable value out of limit");
end Integer;

type Boolean
    _BooleanType_ value;
    parameter _StringType_ quantity = "";
    parameter _BooleanType_ start = false;
    parameter _BooleanType_ fixed;
end Boolean;

type String
    _StringType_ value;
    parameter _StringType_ quantity = "";
    parameter _StringType_ start = "";
    parameter _BooleanType_ fixed;
end String;

/* 4.8.5 Enumeration Types */

/* Some enumeration declared by type E=enumeration(e1, e2, ..., en); */

// type E
//     _EnumType_ value;
//     parameter _StringType_ quantity
//     parameter _EnumType_ min=e1, max=en;
//     parameter _EnumType_ start = e1;
//     parameter _BooleanType_ fixed;
//     constant _EnumType_ e1=...;
//     constant _EnumType_ e2=...;
//     ...
//     constant _EnumType_ en=...;
// equation
//     assert(value >= min and value <= max, "Variable value out of limit");
// end E;

/* 4.8.6 Clock Types */

/* class Clock; */

/* 4.8.8.1 StateSelect */

type StateSelect = enumeration(
    never	"Do not use as state at all.",
    avoid	"Use as state, if it cannot be avoided (but only if
	        variable appears differentiated and no other potential
	        state with attribute default, prefer, or always can be
	        selected).",
    default	"Use as state if appropriate, but only if variable
		appears differentiated.",
    prefer	"Prefer it as state over those having the default
	        value (also variables can be selected, which do not
	        appear differentiated). ",
    always	"Do use it as a state.");

/* 4.8.8.2 ExternalObject */

/* 4.8.8.3 AssertionLevel */

type AssertionLevel=enumeration(warning, error);

/* 4.8.8.4 Connections */

/* 4.8.8.5 Graphical Annotation Types */

/* 9.4.1 Overconstrained Equation Operators for Connection Graphs */

/* ".Connections" is a built-in package in global scope
   containing built-in operators. */

/* 16.8.2 Solver Methods */

/* "The following names of solver methods are standardized:" */

// with ModelicaServices.Types;

// type SolverMethod = String annotation(choices(
//     choice="External"		"Solver specified externally",
//     choice="ExplicitEuler"	"Explicit Euler method (order 1)",
//     choice="ExplicitMidPoint2"	"Explicit mid point rule (order 2)", 
//     choice="ExplicitRungeKutta4" "Explicit Runge-Kutta method (order 4)", 
//     choice="ImplicitEuler"	"Implicit Euler method (order 1)", 
//     choice="ImplicitTrapezoid"	"Implicit trapezoid rule (order 2)"
// ))	"Type of integration method to solve differential equations in
// 	a clocked discretized" + "continuous-time partition.";
