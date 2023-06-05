

axiom df-rab(wph: wff ph, vx: setvar x, cA: class A) {

  return |- "{ x e. A | ph } = { x | ( x e. A /\\ ph ) }";
}
