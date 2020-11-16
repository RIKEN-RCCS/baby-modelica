/* -*-Coding: us-ascii-unix;-*- */

/* It is illegal to depend mutually by extends-clauses.  (Some
   implementation reports an error: "Error: Recursion limit reached in
   instantiation of class M.  Probably caused by mutually dependent
   classes"). */

package P0

/*ILLEGAL*/

model B
    extends M;
    Real v = 10;
end B;

model M
    extends B;
    Real z;
    equation
    z = v;
end M;

end P0;

/* Extending a class defined in a base class is illegal.  Both M0 and
   M1 are illegal.  (some implementation accepts, when the extends
   lines are swapped, that is, extends A comes early. */

package P1

/*ILLEGAL*/

class A
    class B
    end B;
end A;

class M0
    extends M0.B;
    extends A;
end M0;

class M1
    extends B;
    extends A;
end M1;

end P1;
