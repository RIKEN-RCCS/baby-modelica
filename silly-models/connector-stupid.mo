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
