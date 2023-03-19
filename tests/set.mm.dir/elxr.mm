include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cpnf.mm"
include "cmnf.mm"
include "cpr.mm"
include "cun.mm"
include "wo.mm"
include "wceq.mm"
include "w3o.mm"
include "df-xr.mm"
include "eleq2i.mm"
include "elun.mm"
include "pnfex.mm"
include "mnfxr.mm"
include "elexi.mm"
include "elpr2.mm"
include "orbi2i.mm"
include "3orass.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem elxr
  let cA: class A


  assert |- ( A e. RR* <-> ( A e. RR \/ A = +oo \/ A = -oo ) )

  proof
    cA
    cxr
    wcel
    cA
    cr
    cpnf
    cmnf
    cpr
    #
    cun
    #
    wcel
    cA
    cr
    wcel
    #
    cA
    @0
    wcel
    #
    wo
    #
    @2
    cA
    cpnf
    wceq
    #
    cA
    cmnf
    wceq
    #
    w3o
    #
    cxr
    @1
    cA
    df-xr
    eleq2i
    cA
    cr
    @0
    elun
    @4
    @2
    @5
    @6
    wo
    #
    wo
    @7
    @3
    @8
    @2
    cA
    cpnf
    cmnf
    pnfex
    cmnf
    cxr
    mnfxr
    elexi
    elpr2
    orbi2i
    @2
    @5
    @6
    3orass
    bitr4i
    3bitri
end
