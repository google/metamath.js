include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "whe.mm"
include "wb.mm"
include "dffrege69.mm"
include "frege52aid.mm"
include "ax-mp.mm"

theorem frege75
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R x
  disjoint R y
  assert |- ( A. x ( x e. A -> A. y ( x R y -> y e. A ) ) -> R hereditary A )

  proof
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
    #
    cA
    cR
    whe
    #
    wb
    @2
    @3
    wi
    vx
    vy
    cA
    cR
    dffrege69
    @2
    @3
    frege52aid
    ax-mp
end
