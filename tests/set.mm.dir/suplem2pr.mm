include "cnp.mm"
include "wss.mm"
include "cv.mm"
include "cuni.mm"
include "cltp.mm"
include "wbr.mm"
include "wrex.mm"
include "wi.mm"
include "wcel.mm"
include "wn.mm"
include "ltrelpr.mm"
include "brel.mm"
include "simpld.mm"
include "wa.mm"
include "wral.mm"
include "ralnex.mm"
include "wb.mm"
include "ssel2.mm"
include "weq.mm"
include "wo.mm"
include "wor.mm"
include "ltsopr.mm"
include "sotric.mm"
include "mpan.mm"
include "con2bid.mm"
include "ancoms.mm"
include "wpss.mm"
include "ltprord.mm"
include "orbi2d.mm"
include "sspss.mm"
include "equcom.mm"
include "orbi2i.mm"
include "orcom.mm"
include "3bitri.mm"
include "syl6bbr.mm"
include "bitr3d.mm"
include "sylan.mm"
include "an32s.mm"
include "ralbidva.mm"
include "syl5bbr.mm"
include "unissb.mm"
include "ssnpss.mm"
include "biimpd.mm"
include "mpcom.mm"
include "nsyl.mm"
include "syl6bi.mm"
include "con4d.mm"
include "ex.mm"
include "syl5.mm"
include "pm2.43d.mm"
include "elssuni.mm"
include "syl.mm"
include "jctil.mm"

theorem suplem2pr
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vx: setvar x

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint A x
  assert |- ( A C_ P. -> ( ( y e. A -> -. U. A <P y ) /\ ( y <P U. A -> E. z e. A y <P z ) ) )

  proof
    cA
    cnp
    wss
    #
    vy
    cv
    #
    cA
    cuni
    #
    cltp
    wbr
    #
    @1
    vz
    cv
    #
    cltp
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    @1
    cA
    wcel
    #
    @2
    @1
    cltp
    wbr
    #
    wn
    wi
    @0
    @3
    @6
    @3
    @1
    cnp
    wcel
    #
    @0
    @7
    @3
    @10
    @2
    cnp
    wcel
    #
    @1
    @2
    cnp
    cnp
    cltp
    ltrelpr
    brel
    #
    simpld
    @0
    @10
    @7
    @0
    @10
    wa
    #
    @6
    @3
    @13
    @6
    wn
    #
    @2
    @1
    wss
    #
    @3
    wn
    @13
    @14
    @4
    @1
    wss
    #
    vz
    cA
    wral
    #
    @15
    @14
    @5
    wn
    #
    vz
    cA
    wral
    @13
    @17
    @5
    vz
    cA
    ralnex
    @13
    @18
    @16
    vz
    cA
    @0
    @4
    cA
    wcel
    #
    @10
    @18
    @16
    wb
    #
    @0
    @19
    wa
    @4
    cnp
    wcel
    #
    @10
    @20
    cA
    cnp
    @4
    ssel2
    @21
    @10
    wa
    #
    vy
    vz
    weq
    #
    @4
    @1
    cltp
    wbr
    #
    wo
    #
    @18
    @16
    @10
    @21
    @25
    @18
    wb
    @10
    @21
    wa
    #
    @5
    @25
    cnp
    cltp
    wor
    @26
    @5
    @25
    wn
    wb
    ltsopr
    cnp
    @1
    @4
    cltp
    sotric
    mpan
    con2bid
    ancoms
    @22
    @25
    @23
    @4
    @1
    wpss
    #
    wo
    #
    @16
    @22
    @24
    @27
    @23
    @4
    @1
    ltprord
    orbi2d
    @16
    @27
    vz
    vy
    weq
    #
    wo
    @27
    @23
    wo
    @28
    @4
    @1
    sspss
    @29
    @23
    @27
    vz
    vy
    equcom
    orbi2i
    @27
    @23
    orcom
    3bitri
    syl6bbr
    bitr3d
    sylan
    an32s
    ralbidva
    syl5bbr
    vz
    cA
    @1
    unissb
    syl6bbr
    @15
    @1
    @2
    wpss
    #
    @3
    @2
    @1
    ssnpss
    @10
    @11
    wa
    #
    @3
    @30
    @12
    @31
    @3
    @30
    @1
    @2
    ltprord
    biimpd
    mpcom
    nsyl
    syl6bi
    con4d
    ex
    syl5
    pm2.43d
    @8
    @2
    @1
    wpss
    #
    @9
    @8
    @1
    @2
    wss
    @32
    wn
    @1
    cA
    elssuni
    @1
    @2
    ssnpss
    syl
    @11
    @10
    wa
    #
    @9
    @32
    @2
    @1
    cnp
    cnp
    cltp
    ltrelpr
    brel
    @33
    @9
    @32
    @2
    @1
    ltprord
    biimpd
    mpcom
    nsyl
    jctil
end
