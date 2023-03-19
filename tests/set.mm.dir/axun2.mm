include "wel.mm"
include "wa.mm"
include "wex.mm"
include "ax-un.mm"
include "bm1.3ii.mm"

theorem axun2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- E. y A. z ( z e. y <-> E. w ( z e. w /\ w e. x ) )

  proof
    vz
    vw
    wel
    vw
    vx
    wel
    wa
    vw
    wex
    vy
    vz
    vx
    vy
    vz
    vw
    ax-un
    bm1.3ii
end
