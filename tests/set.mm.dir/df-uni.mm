

axiom df-uni(vx: setvar x, vy: setvar y, cA: class A) {

  return |- "U. A = { x | E. y ( x e. y /\\ y e. A ) }";
}
