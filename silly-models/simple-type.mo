/* -*-Coding: us-ascii-unix;-*- */

/* It is illegal to specify a "value" parameter and an initializer
   simultaneously. */

package P0

/*ILLEGAL*/

class M
    Real v(value=1.0)=2.0;
end M;

end P0;

/* Enumerations accept a "value" parameter. */

package P1

type E = enumeration (a,b,c);

class M
    E x(value=E.a);
end M;

end P1;

/* Extending simple-types is OK. */

package P2

class A
    extends Real;
end A;

class M
    A x=10;
end M;

end P2;

/* But, extending simple-types with components are illegal. */

package P3

/*ILLEGAL*/

class A
    extends Real;
    Boolean a=true;
end A;

class M
    A x=10;
end M;

end P3;
