include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wrex.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "peano2rem.mm"
include "wceq.mm"
include "wb.mm"
include "breq1.mm"
include "adantl.mm"
include "ltm1.mm"
include "rspcedvd.mm"
include "rgen.mm"

theorem reltre
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- A. x e. RR E. y e. RR y < x

  proof
    vy
    cv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vy
    cr
    wrex
    vx
    cr
    @1
    cr
    wcel
    #
    @2
    @1
    c1
    cmin
    co
    #
    @1
    clt
    wbr
    #
    vy
    @4
    cr
    @1
    peano2rem
    @0
    @4
    wceq
    @2
    @5
    wb
    @3
    @0
    @4
    @1
    clt
    breq1
    adantl
    @1
    ltm1
    rspcedvd
    rgen
end
