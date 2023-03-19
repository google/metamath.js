
axiom df-acn
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  assert |- AC_ A = { x | ( A e. _V /\ A. f e. ( ( ~P x \ { (/) } ) ^m A ) E. g A. y e. A ( g ` y ) e. ( f ` y ) ) }
end
