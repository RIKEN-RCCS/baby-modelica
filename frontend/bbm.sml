(* bbm.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* Baby-Modelica *)

(* The files "loader", "finder", "seeker", and "syntaxer" implement
   the main part of modifier applications.  The files "operator",
   "folder", and "builder" implement instantiations.  Instantiations
   build an instance_tree, and work not in phases but as a rather
   complex single step.  Later processings proceed in small phases. *)

(* The code is fairly functional, and most of the state is stored in
   instance_tree, loaded_classes, class_bindings and dummy_inners.
   Note that the lexer/parser part is full of state.  The contents of
   the instance_tree evolve in steps. *)

use "hashtable.sml" ;
use "plain.sml" ;
use "setting.sml" ;

use "ast.sml" ;
use "parser.sml" ;
use "lexer.sml" ;

use "common.sml" ;
use "message.sml" ;
use "small0.sml" ;
use "classtree.sml" ;
use "simpletype.sml" ;

use "loader.sml" ;
use "finder.sml" ;
use "seeker.sml" ;
use "refiner.sml" ;
use "syntaxer.sml" ;

use "small1.sml" ;
use "dumper.sml" ;

use "operator.sml" ;
use "folder.sml" ;
use "binder.sml" ;
use "walker.sml" ;
use "builder.sml" ;
use "postbinder.sml" ;

use "connector.sml" ;

use "flatdumper.sml" ;
