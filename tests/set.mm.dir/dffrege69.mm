include "whe.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "dfhe3.mm"
include "bicomi.mm"

theorem dffrege69
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R x
  disjoint R y
  assert |- ( A. x ( x e. A -> A. y ( x R y -> y e. A ) ) <-> R hereditary A )

  proof
    cA
    cR
    whe
    vx
    cv
    #
    cA
    wcel
    @0
    vy
    cv
    #
    cR
    wbr
    @1
    cA
    wcel
    wi
    vy
    wal
    wi
    vx
    wal
    vx
    vy
    cA
    cR
    dfhe3
    bicomi
end
