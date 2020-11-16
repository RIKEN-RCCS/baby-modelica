/* -*-Coding: us-ascii-unix;-*- */

/* A variable declared in a base class is visible in modifiers.  A
   variable is x declared in A and is visible in a modifier A(a=x). */

package P0

/*LEGAL*/

class A
    Real a=0;
    constant Real x=1;
end A;

class M0
    extends X;
    class X=A(a=x);
end M0;

class M1
    extends A(a=x);
end M1;

end P0;
