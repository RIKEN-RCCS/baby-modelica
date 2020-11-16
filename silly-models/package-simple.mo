/* -*-Coding: us-ascii-unix;-*- */

/*
 * A constant array can be declared in a package.
 */

package P0

package P
    constant Real x[3] = {10, 20, 30};
end P;

model M
    Real x = P.x[1];
end M;

end P0;

/*
 * A package cannot be defined as an array (?).  Subscripts to a
 * package are likely ignored.
 */

package P1

/*LEGAL*/

package A
    constant Real c=10;
end A;

package B = A[4];

model M
    Real x = B.c;
end M;

end P1;

/*
 * A class cannot be defined as an array (?).  Replacing "B" with
 * "A[4]" works as intended.  (This is not really a test for packages,
 * but preparatory for packages).
 */

package P2

/*ILLEGAL*/

model A
    Real x=10;
end A;

model B = A[4];

model M
    B b(x={10,11,12,13});
    /*A[4] b(x={10,11,12,13});*/
end M;

end P2;

/*
 * A Real array can be defined.
 */

package P3

type B=Real[4];

model M
    B b(value={10,11,12,13});
end M;

end P3;
