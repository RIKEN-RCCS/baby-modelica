/* -*-Coding: us-ascii-unix;-*- */

/* A just small model. */

model E2
    Real x(start = 1);
    equation
    der(x) = -x + 0.5;
end E2;
