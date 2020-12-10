/* -*-Coding: us-ascii-unix;-*- */

/*
 * Simple example (0).
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

/*
 * A connector may contain a stream record.
 */

package P1

record H
    Real x0, x1;
end H;

connector C
    Real p;
    flow Real m;
    stream H h;
end C;

model S0
    C c;
    equation
    c.p = 10;
    c.m = -10;
    c.h.x0 = 10;
    c.h.x1 = 10;
end S0;

model S1
    C c;
    equation
    c.h.x0 = 20;
    c.h.x1 = 20;
end S1;

model M
    S0 s0;
    S1 s1;
    Real v0, v1;
    equation
    connect(s0.c, s1.c);
    v0 = inStream(s0.c.h.x0);
    v1 = inStream(s1.c.h.x1);
end M;

end P1;

/*
 * Source-pipe-sink.
 */

package P2

connector C
    Real p;
    flow Real m;
    stream Real h;
end C;

model S0
    C c;
    equation
    c.p=10; c.m=-10; c.h=10;
end S0;

model S1
    C c;
    equation
    c.h=20;
end S1;

model P
    C a;
    C b;
    Real h;
    equation
    a.p = b.p;
    0 = a.m + b.m;
    h = semiLinear(a.m, inStream(a.h), inStream(b.h));
    a.h = inStream(b.h);
    b.h = inStream(a.h);
end P;

model M
    S0 s0;
    P p;
    S1 s1;
    Real v0, v1;
    equation
    connect(s0.c, p.a);
    connect(s1.c, p.b);
    v0 = inStream(s0.c.h);
    v1 = inStream(s1.c.h);
end M;

end P2;
