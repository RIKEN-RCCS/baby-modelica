/* -*-Coding: us-ascii-unix;-*- */

/* Ranges can include iterators. */

package P0

class M
    constant Integer s=4;
    Real x[s,s];
    equation
    for i in 1:s, j in 1:i-1 loop
	x[i,j]=j;
    end for;
    for i in 1:s, j in i+1:s loop
	x[i,j]=j;
    end for;
    for i in 1:s loop
	x[i,i]=i;
    end for;
end M;

end P0;

/* A type of a for-iterator is implied by an array index.  An
   enumeration exmaple in 4.8.5 Enumeration Types. */

package P1

type E = enumeration(zero, one, two);

class M
    Real x[E];

    equation
    for e loop
	x[e]=0.0;
    end for;
end M;

end P1;
