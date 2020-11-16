/* -*-Coding: us-ascii-unix;-*- */

/* Trivially illegal, X is declared twice in M. */

package P2

/*ILLEGAL*/

class C Real v=10; end C;
class D Real v=20; end D;

class M
    redeclare class X=D;
    replaceable class X=C;
    X a;
end M;

end P2;
