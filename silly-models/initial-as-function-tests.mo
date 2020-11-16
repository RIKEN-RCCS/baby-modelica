/* -*-Coding: us-ascii-unix;-*- */

/* A simple code with "initial" as an built-in function. */

model E1
    Boolean x;

    equation
    x = initial();
end E1;
