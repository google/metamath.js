include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "wex.mm"
include "wbr.mm"
include "weu.mm"
include "cab.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "imasng.mm"
include "ax-mp.mm"
include "eqeq1i.mm"
include "exbii.mm"
include "euabsn.mm"
include "bitr4i.mm"
include "abbii.mm"

theorem args
  let vx: setvar x
  let vy: setvar y
  let cF: class F

  disjoint F y
  disjoint x y
  assert |- { x | E. y ( F " { x } ) = { y } } = { x | E! y x F y }

  proof
    cF
    vx
    cv
    #
    csn
    cima
    #
    vy
    cv
    #
    csn
    #
    wceq
    #
    vy
    wex
    #
    @0
    @2
    cF
    wbr
    #
    vy
    weu
    #
    vx
    @5
    @6
    vy
    cab
    #
    @3
    wceq
    #
    vy
    wex
    @7
    @4
    @9
    vy
    @1
    @8
    @3
    @0
    cvv
    wcel
    @1
    @8
    wceq
    vx
    vex
    vy
    @0
    cvv
    cF
    imasng
    ax-mp
    eqeq1i
    exbii
    @6
    vy
    euabsn
    bitr4i
    abbii
end
