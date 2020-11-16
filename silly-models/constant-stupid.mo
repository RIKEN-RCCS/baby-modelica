/* -*-Coding: us-ascii-unix;-*- */

/* References to constants are allowed in subcomponents. */

package P0

model A
    Real v=0;
end A;

model B
    Real x=0;
    constant Integer N=4;
end B;

model M
    A a[b.N](each v=20);
    B b(x=30);
end M;

end P0;

/* Classes may depend on an array index.  The value n in A is
   A[i].n=i. */

package P1

model A
    parameter Integer n;
    Real x[n]=fill(10, n);
end A;

constant Integer N=4;

model M
    A a[N](n=1:N);
end M;

end P1;

/* An array dimension depending on its value is illegal. */

package P2

/*ILLEGAL*/

model A
    parameter Integer n;
    Real x[n]=fill(10, n);
end A;

constant Integer N=4;

model M
    A a[a[N].n](n=1:N);
end M;

end P2;

/* Classes may depend on an array index. */

package P3

model A
    parameter Integer n;
    Real x[n]=fill(10, n);
end A;

constant Integer N=4;

model M
    A a0[N](n=1:N);
    A a1[a0[N].n](each n=2);
end M;

end P3;
