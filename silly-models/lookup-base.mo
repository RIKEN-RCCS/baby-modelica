/* -*-Coding: us-ascii-unix;-*- */

/*
 * A lookup of B in M for extends~B, where B is the first part, does
 * not go in the base A.  (Some implementation finds B, while it
 * reports illegal).
 */

package P0

/*ILLEGAL*/

class A
    class B
        Real x=10;
    end B;
end A;

class M
    extends A;
    extends B;
    Real z=x;
end M;

end P0;

/*
 * A lookup of C in A for extends~A.C, which is a remaining part of
 * A.C, goes in the bases of A.
 */

package P1

/*LEGAL*/

class A
    extends B;
end A;

class B
    class C
        Real c=10;
    end C;
end B;

class M
    extends A.C;
    Real z=c;
end M;

end P1;

/*
 * A lookup of C in A for extends~A.C, which is a remaining part of
 * A.C, does not go in the imports of A.
 */

package P2

/*ILLEGAL*/

class A
    import B.C;
end A;

class B
    class C
        Real c=20;
    end C;
end B;

class M
    extends A.C;
    Real z=c;
end M;

end P2;
