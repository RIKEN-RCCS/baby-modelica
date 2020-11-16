/* -*-Coding: us-ascii-unix;-*- */

/* A simple code with "end" as a subscript. */

model E0
    Real x[4] = {0, 0, 0, 0};
    Real v;

    function varend
        input Real a[:];
        output Real y;
        algorithm
        y := a[end];
    end varend;

    equation
    v = varend(x);
end E0;
