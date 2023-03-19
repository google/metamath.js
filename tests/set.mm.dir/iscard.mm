include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "con0.mm"
include "wcel.mm"
include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "wral.mm"
include "cardon.mm"
include "eleq1.mm"
include "mpbii.mm"
include "wss.mm"
include "wb.mm"
include "cardonle.mm"
include "eqss.mm"
include "baibr.mm"
include "syl.mm"
include "wa.mm"
include "cdm.mm"
include "onelon.mm"
include "onenon.mm"
include "adantr.mm"
include "cardsdomel.mm"
include "syl2anc.mm"
include "ralbidva.mm"
include "dfss3.mm"
include "syl6rbbr.mm"
include "bitr3d.mm"
include "biadan2.mm"

theorem iscard
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( ( card ` A ) = A <-> ( A e. On /\ A. x e. A x ~< A ) )

  proof
    cA
    ccrd
    cfv
    #
    cA
    wceq
    #
    cA
    con0
    wcel
    #
    vx
    cv
    #
    cA
    csdm
    wbr
    #
    vx
    cA
    wral
    #
    @1
    @0
    con0
    wcel
    @2
    cA
    cardon
    @0
    cA
    con0
    eleq1
    mpbii
    @2
    cA
    @0
    wss
    #
    @1
    @5
    @2
    @0
    cA
    wss
    #
    @6
    @1
    wb
    cA
    cardonle
    @1
    @7
    @6
    @0
    cA
    eqss
    baibr
    syl
    @2
    @5
    @3
    @0
    wcel
    #
    vx
    cA
    wral
    @6
    @2
    @4
    @8
    vx
    cA
    @2
    @3
    cA
    wcel
    #
    wa
    @3
    con0
    wcel
    cA
    ccrd
    cdm
    wcel
    #
    @4
    @8
    wb
    cA
    @3
    onelon
    @2
    @10
    @9
    cA
    onenon
    adantr
    @3
    cA
    cardsdomel
    syl2anc
    ralbidva
    vx
    cA
    @0
    dfss3
    syl6rbbr
    bitr3d
    biadan2
end
