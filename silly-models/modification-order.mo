/* -*-Coding: us-ascii-unix;-*- */

/* A latter application of modifiers has a precedence. */

/* A modifier on a compoment is latter than a modifier on a class.  It
   includes a "value" modifier.  */

package P0

class A
    class X = Real;
    X x0;		/* a.x0=10 */
    X x1=20;		/* a.x1=20 */
    X x2 (value=20);	/* a.x2=20 */
end A;

class M
    A a (X (value=10));
end M;

end P0;

/* A modifier on a compoment (v=30) is effective after a redeclaration
   on a compoment.  But, A modifier on a class does not remain after a
   redeclaration on a class. */

package P1

class C Real v=10; end C;
class D Real v=20; end D;

class A
    replaceable C a (v=30);
end A;

class B
    replaceable class X = C (v=30);
    X b0;
    X b1 (v=40);
end B;

class BX
    redeclare class X = D;
    extends B;
end BX;

class M
    class A0 = A (redeclare D a);
    class A1 = A (redeclare D a (v=40));
    A0 a0;		/* a0.a.v=30 */
    A1 a1;		/* a1.a.v=40 */
    class B0 = B (redeclare class X = D);
    class B1 = B (redeclare class X = D (v=50));
    B0 b0;	        /* b0.b0.v=30, b0.b1.v=40 */
    B1 b1;	        /* b1.b0.v=50, b1.b1.v=40 */
    BX bx;	        /* bx.b0.v=20, bx.b1.v=40 */
end M;

end P1;

/* A modifier on an extending attaches a modifier a component. */

package P2

class C Real v=10; end C;
class D Real v=20; end D;

class A
    replaceable class X = C;
    X a;	        /* a.v=30 */
    X b (v=40); 	/* b.v=40 */
    X c;	        /* c.v=50 */
    X d (v=40);	        /* d.v=50 */
end A;

class M
    redeclare class X = D (v=30);
    extends A (c.v=50, d.v=50);
end M;

end P2;

/* An elemental redeclaration works like a redeclaration in
   modifiers. */

package P3

class C Real v=10; end C;
class D Real v=20; end D;

class A
    replaceable C a (v=30);
end A;

class B
    replaceable class X = C (v=30);
    X b;
end B;

class X0
    extends A (redeclare D a);
end X0;

class X1
    extends A (redeclare D a (v=40));
end X1;

class X2
    redeclare class X = D;
    extends B;
end X2;

class X3
    redeclare class X = D (v=40);
    extends B;
end X3;

class M
    X0 x0;		/* x0.a.v=30 */
    X1 x1;		/* x1.a.v=40 */
    X2 x2;		/* x2.b.v=20 */
    X3 x3;		/* x2.b.v=40 */
    X0 x4 (a.v=50);	/* x2.a.v=50 */
end M;

end P3;

/* More cases. */

package P4

class C Real v=10; end C;
class D Real v=20; end D;

class A
    replaceable C a (v=30);
end A;

class B
    replaceable class X = C (v=30);
    X b;
end B;

class M
    class A0 = A;
    class A1 = A (redeclare D a);
    class A2 = A (redeclare D a (v=40));
    /*class A3 = A (redeclare D a (v=40), a (v=50));*/
    A0 a0;		/* a0.a.v=30 */
    A1 a1;		/* a1.a.v=30 */
    A2 a2;		/* a0.a.v=40 */
    class B0 = B;
    class B1 = B (redeclare class X = D);
    class B2 = B (redeclare class X = D (v=40));
    class B3 = B (redeclare class X = D (v=40), b (v=50));
    B0 b0;	        /* b0.b.v=30 */
    B1 b1;	        /* b1.b.v=30 */
    B2 b2;	        /* b0.b.v=40 */
    B3 b3;	        /* b1.b.v=50 */
end M;

end P4;
