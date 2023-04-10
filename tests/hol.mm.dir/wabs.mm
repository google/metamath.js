
axiom wabs(hal: $type$ al, hbe: $type$ be, ta: $term$ A, tb: $term$ B, tf: $term$ F, tr: $term$ R) {
  assume ax-tdef.1: $|- B : al$;
  assume ax-tdef.2: $|- F : ( al -> bool )$;
  assume ax-tdef.3: $|- T. |= ( F B )$;
  assume ax-tdef.4: $|- typedef be ( A , R ) F$;

  return $|- A : ( al -> be )$;
}
