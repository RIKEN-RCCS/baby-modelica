/* -*-Coding: us-ascii-unix;-*- */

/*
 * A class B is used as a package in B.C, and a declaration C c1 in B
 * is ignored.  (Some implementation requires an "encapsulated" to C,
 * see below).
 */

package P0

/*LEGAL*/

model A
    model B
        encapsulated model C
            Real x=10;
        end C;
        C c1; /*!*/
    end B;
    B.C c0;
end A;

model M
    A a;
end M;

end P0;

/* 
 * The same as above but without an "encapsulated".
 */

package P1

/*ILLEGAL?*/

model A
    model B
        model C
            Real x=10;
        end C;
        C c; /*!*/
    end B;
    B.C c;
end A;

model M
    A a;
end M;

end P1;
