/* -*-Coding: us-ascii-unix;-*- */

/* Modifiers do not admit array indexing. */

package P0

/*ILLEGAL*/

model A
    Real x[3];
end A;

model M
    A b (x[1]=10);
end M;

end P0;
