/* -*-Coding: us-ascii-unix;-*- */

/* notes.tex label={mixed-class-instance-reference} */

/* It is OK to refer to a constant in a package via a variable
   name. */

package P0

model A1
    package A0
        constant Real c=10;
    end A0;
    Real x0=20;
end A1;

model A2
    A1 a1;
end A2;

model M
    A2 a2;
    Real x=a2.a1.A0.c;
end M;

end P0;

/* Change A0 to a model from a package in P0. */

package P1

model A1
    model A0
        constant Real c=10;
    end A0;
    Real x0=20;
end A1;

model A2
    A1 a1;
end A2;

model M
    A2 a2;
    Real x=a2.a1.A0.c;
end M;

end P1;

/* It is illegal to refer to a class via a variable name. */

package P2

/*ILLEGAL*/

model A1
    model A0
        Real z=10;
    end A0;
end A1;

model A2
    A1 a1;
end A2;

model M
    A2 a2;
    a2.a1.A0 a0;
end M;

end P2;
