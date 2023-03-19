include "ccnv.mm"
include "wfun.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "wrel.mm"
include "relcnv.mm"
include "dffun6.mm"
include "mpbiran.mm"
include "vex.mm"
include "brcnv.mm"
include "mobii.mm"
include "albii.mm"
include "bitri.mm"

theorem funcnv2
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( Fun `' A <-> A. y E* x x A y )

  proof
    cA
    ccnv
    #
    wfun
    #
    vy
    cv
    #
    vx
    cv
    #
    @0
    wbr
    #
    vx
    wmo
    #
    vy
    wal
    #
    @3
    @2
    cA
    wbr
    #
    vx
    wmo
    #
    vy
    wal
    @1
    @0
    wrel
    @6
    cA
    relcnv
    vy
    vx
    @0
    dffun6
    mpbiran
    @5
    @8
    vy
    @4
    @7
    vx
    @2
    @3
    cA
    vy
    vex
    vx
    vex
    brcnv
    mobii
    albii
    bitri
end
