/* -*-Coding: us-ascii-unix;-*- */

/*
 * Referencing a variable in an enclosing class is illegal.  M (or A)
 * as a target model is illegal.  Lexically visible ones should be
 * constants.  It is legal when "x" is a constant.
 */

package P0

/*ILLEGAL*/

model M
    Real x = 10;

    model A
	Real v;
	equation
	v = x;
    end A;

    A a;
end M;

end P0;

/*
 * Class B is visible in M thought a base A of an enclosing C.
 */

package P1

/*LEGAL*/

model A
    model B
	Real x=10;
    end B;
end A;

model C
    extends A;
    model M
	extends B;
	Real z=x;
    end M;
end C;

end P1;

/*
 * A protected class is visible in the present class.
 */

package P2

/*LEGAL*/

protected
model B
    Real x=10;
end B;

public
model M
    B b;
end M;

end P2;

/*
 * A name in an enclosing class is not visible through importing or
 * extending.  P.v is not visible in M0 nor M1.
 */

package P3

/*ILLEGAL*/

package P
    constant Real v = 10;
    model A end A;
end P;

model M0
    extends P.A;
    Real z=v;
end M0;

model M1
    import P.A;
    Real z=v;
end M1;

end P3;

/* **** **** **** **** */

/*
 * An enclosing class is associated to each base class.  Different
 * classes are visible by the same name from base classes via
 * enclosing classes.
 */

package P5

package B0
    type T = Real(value=10);
    model B1
	T b;
    end B1;
end B0;

package D0
    type T = Real(value=20);
    model D1
	extends B0.B1;
	T d;
    end D1;
end D0;

model M
    D0.D1 m; /* m.b=10, m.d=20 */
end M;

end P5;

/* **** **** **** **** */

/*
 * The scope of an enclosing class is the defining one.
 */

package P6

package B0
    type T = Real(value=10);
    model B1
	T b;
    end B1;
end B0;

package D0
    extends B0(T(value=20));
end D0;

model M
    D0.B1 m; /* m.b=20 */
end M;

end P6;

/*
 * A short class definition does not change the scope.
 */

package P7

package B0
    type T = Real(value=10);
    model B1
	T b;
    end B1;
end B0;

package D0
    type T = Real(value=20);
    model D1 = B0.B1;
end D0;

model M
    D0.D1 m; /* m.b=10 */
end M;

end P7;

/*
 * A redeclaration keeps the scope.
 */

package P8

package B0
    type T = Real(value=10);
    model B1
	replaceable model B2
	    T x;
	end B2;
	B2 b;
    end B1;
end B0;

package D0
    type T = Real(value=20);
    model D1
	extends B0.B1;
	model D2
	    T x;
	end D2;
	redeclare model B2=D2;
    end D1;
end D0;

model M
    D0.D1 m;  /* m.b.x=20 */
end M;

end P8;

/*
 * A extends-redeclaration keeps the scope.
 */

package P9

package B0
    type T = Real(value=10);
    model B1
	replaceable model B2
	    T b;
	end B2;
	B2 x;
    end B1;
end B0;

package D0
    type T = Real(value=20);
    model D1
	extends B0.B1;
	redeclare model extends B2
	    T d;
	end B2;
    end D1;
end D0;

model M
    D0.D1 m;  /* m.x.b=10, m.x.d=20 */
end M;

end P9;
