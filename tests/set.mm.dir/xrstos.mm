include "cxrs.mm"
include "ctos.mm"
include "wcel.mm"
include "cpo.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wo.mm"
include "cxr.mm"
include "wral.mm"
include "xrsex.mm"
include "xrsbas.mm"
include "xrsle.mm"
include "xrleid.mm"
include "wa.mm"
include "wceq.mm"
include "xrletri3.mm"
include "biimprd.mm"
include "xrletr.mm"
include "isposi.mm"
include "xrletri.mm"
include "rgen2a.mm"
include "istos.mm"
include "mpbir2an.mm"

theorem xrstos
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- RR*s e. Toset

  proof
    cxrs
    ctos
    wcel
    cxrs
    cpo
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    @1
    @0
    cle
    wbr
    #
    wo
    #
    vy
    cxr
    wral
    vx
    cxr
    wral
    vx
    vy
    vz
    cxr
    cxrs
    cle
    xrsex
    xrsbas
    xrsle
    @0
    xrleid
    @0
    cxr
    wcel
    @1
    cxr
    wcel
    wa
    @0
    @1
    wceq
    @2
    @3
    wa
    @0
    @1
    xrletri3
    biimprd
    @0
    @1
    vz
    cv
    xrletr
    isposi
    @4
    vx
    vy
    cxr
    @0
    @1
    xrletri
    rgen2a
    vx
    vy
    cxr
    cxrs
    cle
    xrsbas
    xrsle
    istos
    mpbir2an
end
