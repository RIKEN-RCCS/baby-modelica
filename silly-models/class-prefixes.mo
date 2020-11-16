/* -*-Coding: us-ascii-unix;-*- */

/* Usage of encapsulated/final/partial. */

package P0

/* Usual use of encapsulated. */

/*LEGAL*/

class A
    encapsulated class B
       Real b=10;
    end B;
end A;

class M
    A.B x;
end M;

end P0;

/* ==== ==== */

package P1

/* Use of encapsulated to a short-class-defintion. */

/*ILLEGAL*/

class A
    encapsulated class C = B;
    class B
       Real b=10;
    end B;
end A;

class M
    A.C x;
end M;

/*
 * (error message from some implementation)
 * Warning: Encapsulation of P0.A.C prevented us from finding B in
 * scope P0.A.C.
 */

end P1;

/* ==== ==== */

package P3

/* Usual use of final class. */

/*LEGAL*/

final class A
    Real a=10;
end A;

final class B
    extends A;
end B;

class M
    B x (a=20);
end M;

end P3;
