include "cc0.mm"
include "cxrs.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "wtru.mm"
include "cxr.mm"
include "cxad.mm"
include "cbs.mm"
include "xrsbas.mm"
include "a1i.mm"
include "cplusg.mm"
include "xrsadd.mm"
include "wcel.mm"
include "0xr.mm"
include "cv.mm"
include "co.mm"
include "xaddid2.mm"
include "adantl.mm"
include "xaddid1.mm"
include "grpidd.mm"
include "trud.mm"

theorem xrs0
  let vx: setvar x


  assert |- 0 = ( 0g ` RR*s )

  proof
    cc0
    cxrs
    c0g
    cfv
    wceq
    wtru
    vx
    cxr
    cxad
    cxrs
    cc0
    cxr
    cxrs
    cbs
    cfv
    wceq
    wtru
    xrsbas
    a1i
    cxad
    cxrs
    cplusg
    cfv
    wceq
    wtru
    xrsadd
    a1i
    cc0
    cxr
    wcel
    wtru
    0xr
    a1i
    vx
    cv
    #
    cxr
    wcel
    #
    cc0
    @0
    cxad
    co
    @0
    wceq
    wtru
    @0
    xaddid2
    adantl
    @1
    @0
    cc0
    cxad
    co
    @0
    wceq
    wtru
    @0
    xaddid1
    adantl
    grpidd
    trud
end
