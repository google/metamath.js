include "cnzr.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "cuvc.mm"
include "co.mm"
include "ovex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wceq.mm"
include "wi.mm"
include "uvcf1o.mm"
include "wb.mm"
include "f1oeq1.mm"
include "eqcoms.mm"
include "biimpd.mm"
include "syl7.mm"
include "imp.mm"
include "spcimedv.mm"
include "pm2.43i.mm"
include "bren.mm"
include "sylibr.mm"

theorem uvcendim
  let cR: class R
  let cU: class U
  let cI: class I
  let cW: class W
  let vu: setvar u
  assume uvcf1o.u: |- U = ( R unitVec I )


  assert |- ( ( R e. NzRing /\ I e. W ) -> I ~~ ran U )

  proof
    cR
    cnzr
    wcel
    cI
    cW
    wcel
    wa
    #
    cI
    cU
    crn
    #
    vu
    cv
    #
    wf1o
    #
    vu
    wex
    #
    cI
    @1
    cen
    wbr
    @0
    @4
    @0
    @3
    @0
    vu
    cU
    cvv
    cU
    cvv
    wcel
    @0
    cU
    cR
    cI
    cuvc
    co
    cvv
    uvcf1o.u
    cR
    cI
    cuvc
    ovex
    eqeltri
    a1i
    @0
    @2
    cU
    wceq
    #
    @0
    @3
    wi
    @0
    cI
    @1
    cU
    wf1o
    #
    @0
    @5
    @3
    cR
    cU
    cI
    cW
    uvcf1o.u
    uvcf1o
    @5
    @6
    @3
    wi
    wi
    @0
    @5
    @6
    @3
    @6
    @3
    wb
    cU
    @2
    cI
    @1
    cU
    @2
    f1oeq1
    eqcoms
    biimpd
    a1i
    syl7
    imp
    spcimedv
    pm2.43i
    cI
    @1
    vu
    bren
    sylibr
end
