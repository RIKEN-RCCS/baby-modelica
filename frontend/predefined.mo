/* predefined.mo -*-Coding: us-ascii-unix;-*- */
/* Copyright (C) 2018-2020 RIKEN R-CCS */

/* Dummy predefined name declarations. */

/* Variables (e.g., "time") cannot be declared in the root namespace
   in Modelica (forbidden by the syntax rules).  Overloaded names of
   conversion functions "Integer", "String", and enumerations cannot
   be defined in Modelica.  Note that a function "sample" is defined
   in two places, in 3.7.3 Event-Related Operators with Function
   Syntax and in 16. Synchronous Language. */

within;

/* 3.6.7 Built-in Variable time */

/*input Real time (final quantity = "Time", final unit = "s");*/

/* 4.8 Predefined Types and Classes */

/* The "fixed" attribute is defined in Real, Integer, Boolean, String,
   and enumerations.  The default to "fixed" is true for
   parameter/constant, and false for other variables.  The "nominal"
   attribute is optional.  The definitions below are not type (it is
   wrong syntactically). */

type Real
    Real value;
    parameter String quantity = "";
    parameter String unit = "";
    parameter String displayUnit = "";
    parameter Real min = -Modelica.Constants.inf;
    parameter Real max = +Modelica.Constants.inf;
    parameter Real start = 0;
    parameter Boolean fixed;
    parameter Real nominal;
    parameter Boolean unbounded = false;
    parameter StateSelect stateSelect = StateSelect.default;
    //equation
    //assert(value >= min and value <= max, "Variable value out of limit");
end Real;

type Integer
    Integer value;
    parameter String quantity = "";
    parameter Integer min = -Modelica.Constants.Integer_inf;
    parameter Integer max = +Modelica.Constants.Integer_inf;
    parameter Integer start = 0;
    parameter Boolean fixed;
    //equation
    //assert(value >= min and value <= max, "Variable value out of limit");
end Integer;

type Boolean
    Boolean value;
    parameter String quantity = "";
    parameter Boolean start = false;
    parameter Boolean fixed;
end Boolean;

type String
    String value;
    parameter String quantity = "";
    parameter String start = "";
    parameter Boolean fixed;
end String;

/* 4.8.5 Enumeration Types */

/*
type E=enumeration(e1, e2, ..., en);
type E
    E value;
    parameter String quantity = "";
    parameter E min = e1;
    parameter E max = en;
    parameter E start = e1;
    parameter Boolean fixed;
    constant E e1; constant E e2; ...
    constant E en;
    equation
    assert(value >= min and value <= max, "Variable value out of limit");
end E;
*/

/* 4.8.6 Clock Types */

class Clock end Clock;

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

type AssertionLevel = enumeration(warning, error);

/* 4.8.8.4 Connections */

/* ".Connections" is a predefined package in the global scope
   containing some functions. */

package Connections
    /*branch*/
    /*root*/
    /*potentialRoot*/
    /*isRoot*/
    /*rooted*/
end Connections;

/* 4.8.8.5 Graphical Annotation Types */

/* 9.4.1 Overconstrained Equation Operators for Connection Graphs */

/* 16.8.2 Solver Methods */

/* "The following names of solver methods are standardized:" */

/* ModelicaServices.Types.SolverMethod; */

/* 3.7 Built-in Intrinsic Operators with Function Syntax */

/* - Mathematical functions and conversion functions (Section 3.7.1) */
/* - Derivative and special purpose operators (Section 3.7.2) */
/* - Event-related operators (Section 3.7.3) */
/* - Array operators/functions (Section 10.1.1) */

/* 12.5 Built-in Functions (there is a same list to above) */

/* - Intrinsic mathematical and conversion functions (Section 3.7.1) */
/* - Derivative and special operators (Section 3.7.2) */
/* - Event-related operators (Section 3.7.3) */
/* - Built-in array functions (Section 10.3) */

/* 3.7.1 Numeric Functions and Conversion Functions */

function abs end abs;
function sign end sign;
function sqrt end sqrt;
/*function Integer end Integer;*/
/*enum*/
/*function String end String;*/

/* 3.7.1.1 Event Triggering Mathematical Functions */

function div end div;
function mod end mod;
function rem end rem;
function ceil end ceil;
function floor end floor;
function integer end integer;

/* 3.7.1.2 Built-in Mathematical Functions and External Built-in Functions */

function sin end sin;
function cos end cos;
function tan end tan;
function asin end asin;
function acos end acos;
function atan end atan;
function atan2 end atan2;
function sinh end sinh;
function cosh end cosh;
function tanh end tanh;
function exp end exp;
function log end log;
function log10 end log10;

/* 3.7.2 Derivative and Special Purpose Operators with Function Syntax */

/* function der end der; */
function delay end delay;
function cardinality end cardinality;
//function homotopy end homotopy;
function semiLinear end semiLinear;
function inStream end inStream;
function actualStream end actualStream;
function spatialDistribution end spatialDistribution;
function getInstanceName end getInstanceName;

function homotopy
    input Real actual;
    input Real simplified;
    output Real y;
    algorithm
    y := actual;
    annotation(Inline = true);
end homotopy;

/* 3.7.3 Event-Related Operators with Function Syntax */

function initial end initial;
function terminal end terminal;
function noEvent end noEvent;
function smooth end smooth;
function sample end sample;
function pre end pre;
function edge end edge;
function change end change;
function reinit end reinit;

/* 8.3.7 assert, 8.3.8 terminate */

function assert end assert;
function terminate end terminate;

/* 10.3 Built-in Array Functions */

function promote end promote;
function ndims end ndims;
function size end size;
function scalar end scalar;
function vector end vector;
function matrix end matrix;
function identity end identity;
function diagonal end diagonal;
function zeros end zeros;
function ones end ones;
function fill end fill;
function linspace end linspace;
function min end min;
function max end max;
function sum end sum;
function product end product;
function transpose end transpose;
function outerProduct end outerProduct;
function symmetric end symmetric;
function cross end cross;
function skew end skew;
function cat end cat;

/* 16. Synchronous Language */

function previous end previous;
/*function sample end sample;*/
function hold end hold;
function subSample end subSample;
function superSample end superSample;
function shiftSample end shiftSample;
function backSample end backSample;
function noClock end noClock;
function firstTick end firstTick;
function interval end interval;

/* 17. State Machines */

function transition end transition;
function initialState end initialState;
function activeState end activeState;
function ticksInState end ticksInState;
function timeInState end timeInState;
