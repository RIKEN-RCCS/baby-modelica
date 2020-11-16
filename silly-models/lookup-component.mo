/* -*-Coding: us-ascii-unix;-*- */

/*
 * A class X defined in M is not visible in a base A.  It is in
 * contrast that redeclaring class X=C is visible from a base
 * class.
 */

package P0

/*ILLEGAL*/

class C Real x = 10; end C;

class A
    X a;
end A;

class M
    class X=C;
    extends A;
end M;

end P0;
