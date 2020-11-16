/* -*-Coding: us-ascii-unix;-*- */

/* A value modifier (x=10) is an equation. */

package P0

/*ILLEGAL*/

class A
    Real x=10;
    equation
    der(x) = -x + 0.5;
end A;

model M
    A a (x(start=1));
end M;

end P0;
