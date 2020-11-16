/* -*-Coding: us-ascii-unix;-*- */

/* An outer works through a redeclaration. */

package P2

class C Real v=10; end C;
class D Real v=20; end D;
class E Real v=30; end E;

class A
    replaceable class X=C;
    X a;
end A;

class B
    redeclare outer class X=D;
    extends A;
end B;

class M
    inner class X=E;
    B b;		/* b.a.v=30 */
end M;

end P2;

/* An outer attached to a replaceable is dropped by a
   redeclaration. */

package P3

class C Real v=10; end C;
class D Real v=20; end D;
class E Real v=30; end E;

class A
    outer replaceable class X=C;
    X a;
end A;

class B
    redeclare class X=D;
    extends A;
end B;

class M
    inner class X=E;
    B b;		/* b.a.x=20 */
end M;

end P3;

