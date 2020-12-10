/* -*-Coding: us-ascii-unix;-*- */

/*
 * Simple example.
 */

package P0

connector C
    Real p;
    flow Real m;
    stream Real h;
end C;

model A0
    C c;
    equation
    c.p = 10;
    c.m = 10;
    c.h = 10;
end A0;

model A1
    C c;
    equation
    c.m = 10;
    c.h = 20;
end A1;

model A2
    C c;
    equation
    c.h = 30;
end A2;

model M
    A0 a0;
    A1 a1;
    A2 a2;
    Real v0, v1, v2;
    equation
    connect(a0.c, a1.c);
    connect(a0.c, a2.c);
    v0 = inStream(a0.c.h);
    v1 = inStream(a1.c.h);
    v2 = inStream(a2.c.h);
end M;

end P0;
