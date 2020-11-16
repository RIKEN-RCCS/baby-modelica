/* -*-Coding: us-ascii-unix;-*- */

/* Unary + on Real is the identity. */

package P0

class M
    constant Real c=-10;
    Real x = +c;
end M;

end P0;

/* Just a simple operator definition. */

package P1

operator record X
    Real x;

    encapsulated operator 'constructor'
	function offset5
	    import P1.X;
	    input Real a0;
	    output X result (x=a0+5);
	    algorithm
	    annotation(Inline=true);
	end offset5;
    end 'constructor';

    encapsulated operator '-'
	function offset10
	    import P1.X;
	    input X a0;
	    output X result;
	    algorithm
	    result := X (a0.x + 10);
	    annotation(Inline=true);
        end offset10;
    end '-';
end X;

class M
    X m0=X(10);	/*m0.x=10+5*/
    X m1=-m0;	/*m1.x=15+10+5*/
end M;

end P1;

/* An operator needs be defined in an operator record. */

package P2

/*ILLEGAL*/

operator record X
    Real x;

    encapsulated operator 'constructor'
	function offset5
	    import P2.X;
	    input Real a0;
	    output X result (x=a0+5);
	    algorithm
	    annotation(Inline=true);
	end offset5;
    end 'constructor';
end X;

    encapsulated operator '-'
	function offset10
	    import P2.X;
	    input X a0;
	    output X result;
	    algorithm
	    result := X (a0.x + 10);
	    annotation(Inline=true);
        end offset10;
    end '-';

class M
    X m0=X(10);	/*m0.x=10+5*/
    X m1=-m0;	/*m1.x=15+10+5*/
end M;

end P2;

/* A binary operator can be defined on the left operand. */

package P3

operator record L
    Real x;

    encapsulated operator '+'
	function add
	    import P3.L;
	    import P3.R;
	    input L a0;
	    input R a1;
	    output L result;
	    algorithm
	    result.x := a0.x + a1.x;
	    annotation(Inline=true);
        end add;
    end '+';
end L;

operator record R
    Real x;
end R;

class M
    L m0(x=10);
    R m1(x=20);
    L m2 = m0 + m1;
end M;

end P3;

/* A binary operator can be defined on the right operand. */

package P4

operator record L
    Real x;
end L;

operator record R
    Real x;

    encapsulated operator '+'
	function add
	    import P4.L;
	    import P4.R;
	    input L a0;
	    input R a1;
	    output L result;
	    algorithm
	    result.x := a0.x + a1.x;
	    annotation(Inline=true);
        end add;
    end '+';
end R;

class M
    L m0(x=10);
    R m1(x=20);
    L m3 = m0 + m1;
end M;

end P4;

/* Unary + is not overloaded. */

package P5

operator record X
    Real x;

    /* Using the default constructor. */

    encapsulated operator '+'
	function add
	    import P5.X;
	    input X a0;
	    output X result;
	    algorithm
	    result := X (a0.x + 100);
	    annotation(Inline=true);
        end add;
    end '+';
end X;

class M
    X m0(x=10);
    X m1=+m0;	/*m1.x=10*/
end M;

end P5;

/* No constructors to predefined types. */

package P6

/*ILLEGAL*/

class M
    Real x0 = Real(10);
end M;

end P6;
