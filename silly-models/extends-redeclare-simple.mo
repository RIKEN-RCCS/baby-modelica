/* -*-Coding: us-ascii-unix;-*- */

/*
 * An extends-redeclaration affects a base like a redeclaration.
 */

package P0

model A Real x=10; end A;

model B
    replaceable model X=A;
    X b; //b.x=10, b.y=10
end B;

model M0
    extends B;
    redeclare model extends X
        Real y=10;
    end X;
end M0;

model M1
    extends B;
    redeclare model X
        Real x=20;
    end X;
end M1;

end P0;

/*
 * An extends-redeclaration should be illegal without a "redeclare".
 * Some implementation seems to add a replaceable/redeclare
 * automatically (check it by restoring the comment-out lines).
 */

package P1

/*ILLEGAL*/

//model A
    model B
        Real x=10;
    end B;
//end A;

model M
    //extends A;
    model extends B (x=20)
        Real y=30;
    end B;
    B a;
end M;

end P1;

/*
 * The scope of an enclosing class is usual.
 */

package P2

package B0
    type T = Real(value=10);
    model B1
	replaceable model B2
	     T b;
        end B2;
    end B1;
end B0;

package D0
    type T = Real(value=20);
    model D1
        extends B0.B1;
        redeclare model extends B2()
        end B2;
        B2 d;
    end D1;
end D0;

model M
    D0.D1 m; /* m.d.b=10 */
end M;

end P2;
