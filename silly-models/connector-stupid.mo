/* -*-Coding: us-ascii-unix;-*- */

/*
 * Nested connectors.  An embedded one is also connected.
 *
 * m0.x1 = 1;
 * m0.c0.x0 = 2;
 * m1.c0.x0 = m0.c0.x0;
 * m1.x1 = m0.x1;
 */

package P5

connector C0
    Real x0;
end C0;

connector C1
    C0 c0;
    Real x1;
end C1;

model M
    C1 m0;
    C1 m1;
    equation
    m0.x1=1;
    m0.c0.x0=2;
    connect (m0, m1);
end M;

end P5;

/*
 * Cardinality of connections.  Cardinality is a count of connect.
 */

package P7

connector C0
    Real x0;
end C0;

model A
    C0 c0;
    equation
    assert (cardinality(c0) == 1 or cardinality(c0) == 3, "outside connectors");
end A;

model M
    A a0;
    A a1;
    A a2;
    A a3;
    equation
    a0.c0.x0=1;
    connect (a0.c0, a1.c0);
    connect (a0.c0, a2.c0);
    connect (a0.c0, a3.c0);
    equation
    assert (cardinality(a0.c0) == 3, "inside connectors");
    assert (cardinality(a1.c0) == 1, "inside connectors");
    assert (cardinality(a2.c0) == 1, "inside connectors");
    assert (cardinality(a3.c0) == 1, "inside connectors");
end M;

end P7;

/*
 * Cardinality of connections.  Taking cardinality of a model's
 * outside connector is allowed (?).
 */

package P8

connector C
    Real x0;
end C;

model M
    C c0;
    C c1;
    C c2;
    C c3;
    equation
    c0.x0=1;
    connect (c0, c1);
    connect (c0, c2);
    connect (c0, c3);
    equation
    assert (cardinality(c0) == 3, "outside connector");
end M;

end P8;

/*
 * Cardinality of connections.  Cardinality of an embedded connector
 * is counted.
 */

package P9

connector C0
    Real x0;
end C0;

connector C1
    C0 d0;
end C1;

model A
    C1 c0;
end A;

model M
    A a0;
    A a1;
    A a2;
    A a3;
    equation
    a0.c0.d0.x0=1;
    connect (a0.c0, a1.c0);
    connect (a0.c0, a2.c0);
    connect (a0.c0, a3.c0);
    equation
    assert (cardinality(a0.c0) == 3, "inside connector");
    assert (cardinality(a0.c0.d0) == 3, "embedded connection");
end M;

end P9;
