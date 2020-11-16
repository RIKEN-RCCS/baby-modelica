/* -*-Coding: us-ascii-unix;-*- */

/*
 * An initializer with idential components is allowed.
 */

package P0

model B
    Real v0=10;
end B;

model S
    extends B;
    model X Real x; end X;
end S;

model M
    B x0;
    S x1=x0;
end M;

end P0;

/*
 * An initializer needs idential components.  An initializer of a
 * class and its base is not allowed: subclass=base case.
 */

package P1

/*ILLEGAL*/

model B
    Real v0=10;
end B;

model S
    extends B;
    Real v1=20;
end S;

model M
    B x0;
    S x1=x0;
end M;

end P1;

/*
 * An initializer needs idential components.  Constants does matter.
 */

package P2

/*ILLEGAL*/

model B
    Real v0=10;
end B;

model S
    extends B;
    constant Real v1=20;
end S;

model M
    B x0;
    S x1=x0;
end M;

end P2;

/*
 * An initializer needs idential components.  An initializer of a
 * class and its base is not allowed: base=subclass case.
 */

package P3

/*ILLEGAL*/

model B
    Real v0=10;
end B;

model S
    extends B;
    Real v1=20;
end S;

model M
    S x0;
    B x1=x0;
end M;

end P3;

/*
 * An initializer with other modifiers.  The modifiers are ignored.
 */

package P4

/*ILLEGAL*/

model B
    Real v0=10;
    Real v1=20;
end B;

model M
    B x0;
    B x1(v1=30)=x0;
end M;

end P4;
