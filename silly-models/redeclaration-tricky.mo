/* -*-Coding: us-ascii-unix;-*- */

/* A class redeclaration in elements and one in modifiers work
   differently.  A modifier on a replaceable class (v=30) is dropped
   on an elemental case. */

package P0

/* (Checked on: Dymola Version 2020 (64-bit), 2019-04-10) */

class C Real v=10; end C;
class D Real v=20; end D;

class A
    replaceable class X=C (v=30);
    X x;
end A;

class A0=A (redeclare class X=D);

class A1
    redeclare class X=D;
    extends A;
end A1;

class A2
    extends A (redeclare class X=D);
end A2;

class M
    A0 a0;      /* a0.x.v=30 */
    A1 a1;      /* a1.x.v=20 */
    A2 a2;      /* a1.x.v=30 */
end M;

end P0;

/* A component redeclaration case. */

package P1

/* (Checked on: Dymola Version 2020 (64-bit), 2019-04-10) */

class C Real v=10; end C;
class D Real v=20; end D;

class A
    replaceable C x (v=30);
end A;

class A0=A (redeclare D x);

class A1
    redeclare D x;
    extends A;
end A1;

class A2
    extends A (redeclare D x);
end A2;

class M
    A0 a0;      /* a0.x.v=30 */
    A1 a1;      /* a1.x.v=20 */
    A2 a2;      /* a1.x.v=30 */
end M;

end P1;

/* Expected result case: A component redeclaration with modifiers. */

package P2

class C Real v=10; end C;
class D Real v=20; end D;

class A
    replaceable C x (v=30);
end A;

class A0=A (redeclare D x (v=40));

class A1
    redeclare D x (v=40);
    extends A;
end A1;

class A2
    extends A (redeclare D x (v=40));
end A2;

class M
    A0 a0;      /* a0.x.v=40 */
    A1 a1;      /* a1.x.v=40 */
    A2 a2;      /* a1.x.v=40 */
end M;

end P2;
