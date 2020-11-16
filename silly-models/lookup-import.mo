/* -*-Coding: us-ascii-unix;-*- */

/*
 * Imports does not include the imports of the imports.  C in B for
 * import~B.C is not visible.
 */

package P0

/*ILLEGAL*/

class A
    class C
        Real x=10;
    end C;
end A;

class B
    import A.C;
end B;

class M
    //import A.C;
    import B.C;
    A m;
end M;

end P0;

/*
 * A lookup of C in B for import~B.C, which is a remaining part of
 * B.C, goes to the base A.  C is visible through a base A of B.
 */

package P1

/*LEGAL*/

class A
    class C
        Real x=10;
    end C;
end A;

class B
    extends A;
end B;

class M
    import B.C;
    A m;
end M;

end P1;

/*
 * C, which is imported in A, is not visible in a lookup of C in A for
 * the declaration A.C~z, where C is a remaining part A.C.
 */

package P2

/*ILLEGAL*/

class A
    import B.C;
end A;

class B
    class C
        Real c=10;
    end C;
end B;

class M
    A.C z;
end M;

end P2;
