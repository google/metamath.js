include "omex.mm"
include "inf0.mm"

theorem axinf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  assert |- E. y ( x e. y /\ A. z ( z e. y -> E. w ( z e. w /\ w e. y ) ) )

  proof
    vx
    vy
    vz
    vw
    omex
    inf0
end
