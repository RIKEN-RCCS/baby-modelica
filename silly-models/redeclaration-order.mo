/* -*-Coding: us-ascii-unix;-*- */

/* A redeclaration X=D in M is effective over a redeclaration X=E in a
   modifier.  It is because a redeclaration X=E in a modifier is
   applied earlier than a redeclaration X=D. */

package P0

class C Real v=10; end C;
class D Real v=20; end D;
class E Real v=30; end E;

class A
    replaceable class X=C;
    X a;		/* X=D */
end A;

class M
    redeclare replaceable class X=D;
    extends A (redeclare replaceable class X=E);
end M;

end P0;

/* A redeclaration X=E in M is effective over X=D in B.  It is because
   a redeclaration X=D is applied earlier than X=E. */

package P1

class C Real v=10; end C;
class D Real v=20; end D;
class E Real v=30; end E;

class A
    replaceable class X=C;
    X a;		/* X=E */
end A;

class B
    redeclare replaceable class X=D;
    extends A;
end B;

class M
    redeclare replaceable class X=E;
    extends B;
end M;

end P1;
