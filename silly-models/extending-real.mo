/* -*-Coding: us-ascii-unix;-*- */

/* It is illegal to extend and to add an element to Real.  Types
   cannot contain additional elements. */

package P0

/*ILLEGAL*/

type A
    extends Real;
    Real v=10;
end A;

model M
    A x=20;
end M;

end P0;
