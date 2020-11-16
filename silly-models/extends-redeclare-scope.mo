/* -*-Coding: us-ascii-unix;-*- */

/* The scope of modifiers to an extends-redeclaration is the
   redeclared class.  x and y are visible from a modifier. */

package P0

class E
    replaceable class A
	Real a=10;
	Real x=20;
    end A;
end E;

class M
    extends E;
    redeclare class extends A (a=x+y)
	Real y=30;
    end A;
    A m;
end M;

end P0;

package P1

class E
    replaceable class A
        replaceable class X
	    Real x=10;
	end X;
	class B
	    Real x=20;
	end B;
	X a;
    end A;
end E;

class M
    extends E;
    redeclare class extends A (redeclare class X=B)
    end A;
    A m;
end M;

end P1;

/* The scope of modifiers to an extends-redeclaration does not include
   the class (which is the scope, usually). */

package P2

/*ILLEGAL*/

class E
    replaceable class A
	Real a=10;
    end A;
end E;

class M
    extends E;
    redeclare class extends A (a=x+30)
    end A;
    Real x=20;
    A m;
end M;

end P2;

/* The scope of modifiers to a usual definition does not include the
   class. */

package P4

/*ILLEGAL*/

class A
   Real a=10;
   Real x=20;
end A;

class M
    class B = A (a=x+30);
    B m;
end M;

end P4;
