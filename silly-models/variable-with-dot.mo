/* -*-Coding: us-ascii-unix;-*- */

/* It is not allowed a dot to refer to a global variable. */

/* ILLEGAL */

model M
    Real x;
    equation
    x = .time;
end M;
