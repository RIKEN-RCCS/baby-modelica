/* -*-Coding: us-ascii-unix;-*- */

/* pure expression takes an argument list. */

package P0

/*ILLEGAL*/

model M
    Real x;
    equation
    x = pure(1.0);
end M;

end P0;
