/* -*-Coding: us-ascii-unix;-*- */

/* Sizes of arrays in states be constants. */

package P0

/*ILLEGAL*/

model M
    Integer v = integer(10 * time + 1);
    Real x[:] = 1:v;
end M;

end P0;

/* A reference case to package P2.  Enumerations can be used as array
   index spaces. */

package P1

model M
    type E = enumeration (thee,four,five);
    Real x[E];
    equation
    for e in E loop
	x[e] = 10;
    end for;
end M;

end P1;

/* Integer classes cannot be used as array index spaces. */

package P2

/*ILLEGAL*/

model M
    type R = Integer(min=3,max=5);
    Real x[R];
end M;

end P2;
