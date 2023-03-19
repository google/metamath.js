include "cxrs.mm"
include "cmgm.mm"
include "wcel.mm"
include "cv.mm"
include "cxad.mm"
include "co.mm"
include "cxr.mm"
include "wral.mm"
include "xaddcl.mm"
include "rgen2a.mm"
include "cc0.mm"
include "wb.mm"
include "0xr.mm"
include "xrsbas.mm"
include "xrsadd.mm"
include "ismgmn0.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem xrsmgm
  let vx: setvar x
  let vy: setvar y


  assert |- RR*s e. Mgm

  proof
    cxrs
    cmgm
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cxad
    co
    cxr
    wcel
    #
    vy
    cxr
    wral
    vx
    cxr
    wral
    #
    @3
    vx
    vy
    cxr
    @1
    @2
    xaddcl
    rgen2a
    cc0
    cxr
    wcel
    @0
    @4
    wb
    0xr
    vx
    vy
    cc0
    cxr
    cxrs
    cxad
    xrsbas
    xrsadd
    ismgmn0
    ax-mp
    mpbir
end
