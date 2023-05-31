

axiom ax-gen(wph: $wff$ ph, vx: $setvar$ x) {
  assume ax-gen.1: $|- ph$;

  return $|-$ $A. x ph$;
}
