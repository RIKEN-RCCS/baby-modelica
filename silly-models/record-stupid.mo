/* -*-Coding: us-ascii-unix;-*- */

/*
 * Redeclaration of Real by Integer (for a variable).  Some
 * implementations warn if a value (v=10) is missing.
 */

package P0

model R0
    replaceable Real v = 10;
end R0;

model M
    model R1 = R0 (redeclare Integer v);
    R1 x (v = 20);
end M;
end P0;

/*
 * Redeclaration keeps a value modifier (v=10).
 */

package P1

model R0
    replaceable Real v = 10;
end R0;

model M
    model R1 = R0 (redeclare Integer v);
    R1 x;
end M;

end P1;

/*
 * Redeclaration of Real by Integer (for a class).  Some
 * implementations accepted it, although they err as illegal.
 */

package P2

model R0
    replaceable type X = Real;
    X v = 10;
end R0;

model M
    model R1 = R0 (redeclare type X = Integer);
    R1 x (v = 20);
end M;

end P2;

/* ================================================================ */

/*
 * Redeclaration of Real by Integer in a record.
 */

package P3

record R0
    replaceable Real v = 10;
end R0;

model M
    record R1 = R0 (redeclare Integer v);
    R1 x (v = 20);
end M;

end P3;

/*
 * Compatibility by named element equality.
 */

package P4

record R0
    replaceable Real v = 10;
end R0;

model M
    record R1 = R0 (redeclare Integer v);
    record R2 = R0 (redeclare Integer v);
    R1 x1 (v = 20);
    R2 x2 = x1;
end M;

end P4;

/*
 * Compatibility by named element equality (with different types).
 */

package P5

record R0
    replaceable Real v = 10;
end R0;

model M
    record R1 = R0 (redeclare Integer v);
    record R2 = R0;
    R1 x1 (v = 20);
    R2 x2 = x1;
end M;

end P5;

/*
 * Compatibility by named element equality (with different types).
 * Some implementations did not accept when R0 and R1 is swapped, by a
 * less variability problem (for Real=Integer).
 */

package P6

record R0
    Real v;
end R0;

record R1
    Integer v;
end R1;

model M
    R1 x1 (v = 20);
    R0 x0 = x1;
end M;

end P6;
