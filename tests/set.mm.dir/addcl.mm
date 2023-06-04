include "ax-addcl.mm";

theorem addcl(cA: 'class' A, cB: 'class' B) {





  do {
    cA;
    cB;
    ax-addcl;
  };

  return '|-' "( ( A e. CC /\\ B e. CC ) -> ( A + B ) e. CC )";
}
