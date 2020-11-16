/* -*-Coding: us-ascii-unix;-*- */

/*
 * A redeclaration works on redeclaring both a class and a component.
 */

package P0

model A Real v=10; end A;
model B Real v=20; end B;
model C Real v=30; end C;
model D Real v=40; end D;

model H
    replaceable model X=A;
    replaceable model Y=B;
    replaceable X a;
end H;

model M
    redeclare Y a;
    redeclare model X=C;
    redeclare model Y=D;
    extends H;  /* a.v=40 */
end M;

end P0;

/*
 * Redeclaring X=D in M affects the X in the base class.  A
 * redeclaration in an element works on a base, while a redeclaration
 * in a modifier works on a class.
 */

package P1

model C Real v=10; end C;
model D Real v=20; end D;

model A
    replaceable model X=C;
    X a;	/* X=D */
end A;

model M0
    redeclare model X=D;
    extends A;
end M0;

model M1
    A m (redeclare model X=D);
end M1;

end P1;

/*
 * A replaceable defined outside is not visible.
 */

package P3

/*ILLEGAL*/

model C Real v=10; end C;
model D Real v=20; end D;

replaceable model X=C;

model A
    X a;
end A;

model M
    extends A (redeclare model X=D);
end M;

end P3;

/*
 * A redeclaration is not a definition.
 */

package P4

/*ILLEGAL*/

model C Real v=10; end C;

model A
    X a;
end A;

model M0
    extends A (redeclare model X=C);
end M0;

model M1
    redeclare model X=C;
    extends A;
end M1;

end P4;

/*
 * An imported name is not replaceable.  It is replaceable, when it is
 * writen as "import~A; replaceable~class~X=A.X;" in B.
 */

package P6

/*ILLEGAL*/

model C Real v=10; end C;
model D Real v=20; end D;

model A
    replaceable model X=C;
end A;

model B
    import X=A.X;
    X a;
end B;

model M
    redeclare model X=D;
    extends B;
end M;

end P6;

/*
 * Trivially, X to be redeclared is missing.
 */

package P8

/*ILLEGAL*/

model C Real v=10; end C;
model D Real v=20; end D;

model A
    replaceable model X=C;
    X a;  /* X=D */
end A;

model M
    redeclare model X=D;
    A m;
end M;

end P8;

/*
 * Trivially illgal, X to be redeclared is missing.
 */

package P9

/*ILLEGAL*/

model C Real v=10; end C;
model D Real v=20; end D;

model A
    redeclare model X=D;
end A;

model M
    replaceable model X=C;
    extends A;
    X a;  /* X=D */
end M;

end P9;

/*
 * A redeclaration overrides a redeclaration.
 */

package P10

model A
    replaceable model X
        Real v=10;
    end X;
    X a;
end A;

model B
    extends A;
    redeclare replaceable model extends X (v=40)
        /*empty*/
    end X;
end B;

model C
    extends B;
    redeclare model X
        Real v=50;
    end X;
end C;

model M
    C c;  /* c.a.v=50 */
end M;

end P10;

/*
 * An inner/outer can be on an elemental redefinition/redeclaration.
 */

package P11

model C Real v=10; end C;

model A
    replaceable model X=C;
    X a;
end A;

model B
    redeclare outer model X
        Real v=20;
    end X;
    extends A;
end B;

model M
    inner model X
        Real v=30;
    end X;
    B b;  /* b.a.v=30 */
end M;

end P11;
