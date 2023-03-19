include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cen.mm"
include "wbr.mm"
include "cardid2.mm"
include "con0.mm"
include "cardon.mm"
include "isnumi.mm"
include "mpan.mm"
include "impbii.mm"

theorem isnum3
  let cA: class A
  let vy: setvar y


  assert |- ( A e. dom card <-> ( card ` A ) ~~ A )

  proof
    cA
    ccrd
    cdm
    wcel
    #
    cA
    ccrd
    cfv
    #
    cA
    cen
    wbr
    #
    cA
    cardid2
    @1
    con0
    wcel
    @2
    @0
    cA
    cardon
    @1
    cA
    isnumi
    mpan
    impbii
end
