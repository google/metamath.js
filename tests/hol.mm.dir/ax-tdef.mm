
axiom ax-tdef(hal: $type$ al, hbe: $type$ be, vx: $var$ x, ta: $term$ A, tb: $term$ B, tf: $term$ F, tr: $term$ R) {
  assume ax-tdef.1: $|- B : al$;
  assume ax-tdef.2: $|- F : ( al -> bool )$;
  assume ax-tdef.3: $|- T. |= ( F B )$;
  assume ax-tdef.4: $|- typedef be ( A , R ) F$;

  return $|-$ $T. |= ( ( ! \ x : be . [ ( A ( R x : be ) ) = x : be ] ) , ( ! \ x : al . [ ( F x : al ) = [ ( R ( A x : al ) ) = x : al ] ] ) )$;
}
