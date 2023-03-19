include "ccnv.mm"
include "wfun.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "funcnv2.mm"
include "vex.mm"
include "brcnv.mm"
include "mobii.mm"
include "albii.mm"
include "bitri.mm"

theorem fun2cnv
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( Fun `' `' A <-> A. x E* y x A y )

  proof
    cA
    ccnv
    #
    ccnv
    wfun
    vy
    cv
    #
    vx
    cv
    #
    @0
    wbr
    #
    vy
    wmo
    #
    vx
    wal
    @2
    @1
    cA
    wbr
    #
    vy
    wmo
    #
    vx
    wal
    vy
    vx
    @0
    funcnv2
    @4
    @6
    vx
    @3
    @5
    vy
    @1
    @2
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
