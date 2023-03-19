include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "crp.mm"
include "wrex.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "rphalfcl.mm"
include "wceq.mm"
include "wb.mm"
include "breq1.mm"
include "adantl.mm"
include "rphalflt.mm"
include "rspcedvd.mm"
include "rgen.mm"

theorem rpltrp
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- A. x e. RR+ E. y e. RR+ y < x

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
    crp
    wrex
    vx
    crp
    @1
    crp
    wcel
    #
    @2
    @1
    c2
    cdiv
    co
    #
    @1
    clt
    wbr
    #
    vy
    @4
    crp
    @1
    rphalfcl
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
    rphalflt
    rspcedvd
    rgen
end
