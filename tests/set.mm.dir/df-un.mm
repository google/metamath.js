

axiom df-un(vx: $setvar$ x, cA: $class$ A, cB: $class$ B) {

  return $|-$ $( A u. B ) = { x | ( x e. A \/ x e. B ) }$;
}
