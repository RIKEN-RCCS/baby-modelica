/* -*-Coding: us-ascii-unix;-*- */

/* Extending a replaceable is illegal.  A case of an elemental
   redeclaration. */

/* (Some implementation accepts this and ignores a redeclaration with
   a warning: "Base class X is replaceable"). */

package P0

/*ILLEGAL*/

class C Real v=10; end C;
class D Real v=20; end D;

class A
    replaceable class X=C;
    extends X;          /* X=C */
end A;

class M
    redeclare class X=D;
    extends A;
end M;

end P0;

/* Extending a replaceable is illegal.  A case of an
   extends-redeclaration. */

package P1

/*ILLEGAL*/

class A Real x=10; end A;

class B
    replaceable class X=A;
    extends X;
end B;

class M
    extends B;
    redeclare class extends X
	Real y=10;
    end X;
end M;

end P1;

/* Extending a replaceable is illegal.  A case of a redeclaration in
   an modifier. */

/* (Some implementation accepts this without warnings). */

package P2

/*ILLEGAL*/

class C Real x=10; end C;
class D Real x=20; end D;

class A
    replaceable class X=C;
    extends X;
end A;

class M
    A a (redeclare class X=D);
end M;

end P2;

/* Extending a replaceable is illegal.  A case of an elemental
   redeclaration. */

/* (Some implementation behaves differently for elemental and modifier
   redeclarations. */

package P3

/*ILLEGAL*/

class C Real x=10; end C;
class D Real x=20; end D;

class A
    replaceable class X=C;
    extends X;
end A;

class B
    redeclare class X=D;
    extends A;
end B;

class M
    B b /*(redeclare class X=D)*/;
end M;

end P3;

/* Extending an replaceable is illegal.  A case of a redeclaration
   in a modifier of an instance. */

package P4

/*ILLEGAL*/

class C Real v=10; end C;
class D Real v=20; end D;

class A
    replaceable class X=C;
    X a;
end A;

class B
    extends A;
end B;

class M
    B b (redeclare class X=D);          /* b.a.v=20 */
end M;

end P4;

/* Extending an replaceable is illegal.  A case of a redeclarations in
   a modifier to an extends-clause. */

class P5

class C Real v=10; end C;
class D Real v=20; end D;

class A
    replaceable class X=C;
    X a;        /* a.v=20 */
end A;

class M
    extends A (redeclare class X=D);
end M;

end P5;
