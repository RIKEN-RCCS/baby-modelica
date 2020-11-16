/* -*-Coding: us-ascii-unix;-*- */

/* ================================================================ */

/* An initializer value to an outer is usually ignored.  A value of an
   outer is used when there is no matching inner to the outer.
   Modifiers even to a final variable are accepted when they are
   ignored. */

package P0

/*LEGAL*/

class A final Real x = 10; end A;

class B
    outer A a (x=20);
end B;

class M
    inner A a;		//a.x=10
    B b;
end M;

end P0;

/* ================================================================ */

/* It works to extend an outer class. */

package P1

/*LEGAL*/

class A0 Real x=10; end A0;
class A1 Real x=20; end A1;

class C
    outer class X = A0;
    extends X;
end C;

class M
    inner class X = A1;
    C c;		//c.x=20
    Real y = c.x;
end M;

end P1;

/* ================================================================ */

/* An outer in a package is just ignored, but its use is legal. */

package P4

/*LEGAL*/

class A0 Real x=10; end A0;
class A1 Real x=20; end A1;

class P
    outer class X = A0;
    class B
       A0 c;
    end B;
end P;

class M
    inner class X = A1;
    P.B b;
    Real y = b.c.x;
end M;

end P4;

/* An outer in a package is just ignored, and it is not visible. */

package P5

/*ILLEGAL*/

class A0 Real x=10; end A0;
class A1 Real x=20; end A1;

class P
    outer class X = A0;
    class B
       X c;
    end B;
end P;

class M
    inner class X = A1;
    P.B b;
    Real y = b.c.x;
end M;

end P5;
