

axiom ax-addass(cA: class A, cB: class B, cC: class C) {

  return |- "( ( A e. CC /\\ B e. CC /\\ C e. CC ) -> ( ( A + B ) + C ) = ( A + ( B + C ) ) )";
}
