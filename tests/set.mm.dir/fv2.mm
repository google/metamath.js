include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "cio.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "cab.mm"
include "cuni.mm"
include "df-fv.mm"
include "dfiota2.mm"
include "eqtri.mm"

theorem fv2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  assert |- ( F ` A ) = U. { x | A. y ( A F y <-> y = x ) }

  proof
    cA
    cF
    cfv
    cA
    vy
    cv
    cF
    wbr
    #
    vy
    cio
    @0
    vy
    vx
    weq
    wb
    vy
    wal
    vx
    cab
    cuni
    vy
    cA
    cF
    df-fv
    @0
    vy
    vx
    dfiota2
    eqtri
end
