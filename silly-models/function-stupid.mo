/* -*-Coding: us-ascii-unix;-*- */

/*
 * (aimless).
 */

package P0

record R0
    replaceable Real v = 10;
end R0;

function F
    record R1 = R0 (redeclare Integer v);
    input R1 a;
    output R1 r;
algorithm
    r.v := a.v + 2;
end F;

model M
    record R1 = R0 (redeclare Integer v);
    R1 x(v=20);
    R1 y = F(x);
end M;

end P0;

/*
 * Local variable initialization by modifiers.
 */

package P1

record R0
    replaceable Real v = 10;
end R0;

function F0
    input R0 a;
    output R0 r;
  protected
    R0 x (v=20);
algorithm
    r.v := x.v + 2;
end F0;

function F1
    input R0 a;
    output R0 r;
  protected
    R0 x (redeclare Integer v) = a;
algorithm
    r.v := x.v + 2;
end F1;

model M
    R0 x(v=20);
    R0 y0 = F0(x);
    R0 y1 = F1(x);
end M;
end P1;
