/* -*-Coding: us-ascii-unix;-*- */

/*
 * A value of a constant by initial equation.
 */

package P0

model M
    parameter Real x0=0; /* OK */

    /* start value only with fixed=false: NG (error). */
    //parameter Real x1 (fixed=false,start=10);

    /* start value only with fixed=true: OK (warning). */
    parameter Real x2 (fixed=true,start=20);

    /* initial equation only, with no fixed: NG. */
    //parameter Real x3;

    /* initial equation only with fixed=false: OK. */
    parameter Real x4 (fixed=false);

    /* start value and initial equation, with fixed=false: OK. */
    parameter Real x5 (fixed=false,start=10);

    initial equation
    //x3=30;
    x4=40;
    x5=50;
end M;

end P0;

/*
 * A constant needs an initializer value.
 */

package P1

/*ILLEGAL*/

model M
    constant Real x0;
    constant Real x1;
    constant Real x2 (start=30);
    constant Real x3=40;
    initial equation
    x0=10;
    x1=20;
end M;

end P1;
