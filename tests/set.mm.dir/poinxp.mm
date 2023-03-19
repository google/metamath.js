include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "cxp.mm"
include "cin.mm"
include "wpo.mm"
include "wcel.mm"
include "wb.mm"
include "brinxp.mm"
include "anidms.mm"
include "ad2antrr.mm"
include "notbid.mm"
include "adantr.mm"
include "adantll.mm"
include "anbi12d.mm"
include "adantlr.mm"
include "imbi12d.mm"
include "ralbidva.mm"
include "ralbiia.mm"
include "df-po.mm"
include "3bitr4i.mm"

theorem poinxp
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R Po A <-> ( R i^i ( A X. A ) ) Po A )

  proof
    vx
    cv
    #
    @0
    cR
    wbr
    #
    wn
    #
    @0
    vy
    cv
    #
    cR
    wbr
    #
    @3
    vz
    cv
    #
    cR
    wbr
    #
    wa
    #
    @0
    @5
    cR
    wbr
    #
    wi
    #
    wa
    #
    vz
    cA
    wral
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    @0
    @0
    cR
    cA
    cA
    cxp
    cin
    #
    wbr
    #
    wn
    #
    @0
    @3
    @13
    wbr
    #
    @3
    @5
    @13
    wbr
    #
    wa
    #
    @0
    @5
    @13
    wbr
    #
    wi
    #
    wa
    #
    vz
    cA
    wral
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    cA
    cR
    wpo
    cA
    @13
    wpo
    @12
    @23
    vx
    cA
    @0
    cA
    wcel
    #
    @11
    @22
    vy
    cA
    @24
    @3
    cA
    wcel
    #
    wa
    #
    @10
    @21
    vz
    cA
    @26
    @5
    cA
    wcel
    #
    wa
    #
    @2
    @15
    @9
    @20
    @28
    @1
    @14
    @24
    @1
    @14
    wb
    #
    @25
    @27
    @24
    @29
    @0
    @0
    cA
    cA
    cR
    brinxp
    anidms
    ad2antrr
    notbid
    @28
    @7
    @18
    @8
    @19
    @28
    @4
    @16
    @6
    @17
    @26
    @4
    @16
    wb
    @27
    @0
    @3
    cA
    cA
    cR
    brinxp
    adantr
    @25
    @27
    @6
    @17
    wb
    @24
    @3
    @5
    cA
    cA
    cR
    brinxp
    adantll
    anbi12d
    @24
    @27
    @8
    @19
    wb
    @25
    @0
    @5
    cA
    cA
    cR
    brinxp
    adantlr
    imbi12d
    anbi12d
    ralbidva
    ralbidva
    ralbiia
    vx
    vy
    vz
    cA
    cR
    df-po
    vx
    vy
    vz
    cA
    @13
    df-po
    3bitr4i
end
