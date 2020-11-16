/* -*-Coding: us-ascii-unix;-*- */

/* ndims and size.  ndims(A)=0 and size(A)={} on a scalar.  "y" is
   empty (and not defined) in this case. */

package P0

model M
    Real A = 10;
    Integer x = ndims(A);
    Integer y[:] = size(A);
end M;

end P0;
