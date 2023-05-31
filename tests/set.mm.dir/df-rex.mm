

axiom df-rex(wph: $wff$ ph, vx: $setvar$ x, cA: $class$ A) {

  return $|-$ $( E. x e. A ph <-> E. x ( x e. A /\ ph ) )$;
}
