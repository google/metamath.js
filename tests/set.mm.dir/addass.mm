include "ax-addass.mm";

theorem addass(cA: class A, cB: class B, cC: class C) {





  do {
    cA;
    cB;
    cC;
    ax-addass;
  };

  return |- "( ( A e. CC /\\ B e. CC /\\ C e. CC ) -> ( ( A + B ) + C ) = ( A + ( B + C ) ) )";
}
