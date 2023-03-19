include "chil.mm"
include "wcel.mm"
include "cph.mm"
include "co.mm"
include "wn.mm"
include "wa.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cin.mm"
include "cv.mm"
include "elin.mm"
include "wi.mm"
include "cva.mm"
include "wceq.mm"
include "wrex.mm"
include "csh.mm"
include "wb.mm"
include "chshii.mm"
include "spansnsh.mm"
include "shsel.mm"
include "sylancr.mm"
include "c0v.mm"
include "cmv.mm"
include "cheli.mm"
include "elspansncl.mm"
include "w3a.mm"
include "hvsubadd.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "syl3an.mm"
include "3expa.mm"
include "shsvsi.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "adantr.mm"
include "sylbird.mm"
include "exp32.mm"
include "com4r.mm"
include "imp31.mm"
include "adantrr.mm"
include "shscli.mm"
include "elspansn5.mm"
include "ax-mp.mm"
include "adantl.mm"
include "mpdd.mm"
include "oveq2.mm"
include "ax-hvaddid.mm"
include "sylan9eqr.mm"
include "sylan.mm"
include "eqeq2d.mm"
include "adantll.mm"
include "biimpac.mm"
include "biimparc.mm"
include "biimpri.mm"
include "ancoms.mm"
include "sylan2.mm"
include "expr.mm"
include "ad2antrl.mm"
include "mpd.mm"
include "a1d.mm"
include "ex.mm"
include "com23.mm"
include "com4l.mm"
include "imp4c.mm"
include "exp4a.mm"
include "expd.mm"
include "rexlimdvv.mm"
include "sylbid.mm"
include "imp4b.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "wss.mm"
include "shsub1.mm"
include "ssrin.mm"
include "syl.mm"
include "eqssd.mm"

theorem sumdmdlem
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume sumdmdi.1: |- A e. CH
  assume sumdmdi.2: |- B e. CH


  assert |- ( ( C e. ~H /\ -. C e. ( A +H B ) ) -> ( ( B +H ( span ` { C } ) ) i^i A ) = ( B i^i A ) )

  proof
    cC
    chil
    wcel
    #
    cC
    cA
    cB
    cph
    co
    #
    wcel
    wn
    #
    wa
    #
    cB
    cC
    csn
    cspn
    cfv
    #
    cph
    co
    #
    cA
    cin
    #
    cB
    cA
    cin
    #
    @3
    vy
    @6
    @7
    vy
    cv
    #
    @6
    wcel
    @8
    @5
    wcel
    #
    @8
    cA
    wcel
    #
    wa
    @3
    @8
    @7
    wcel
    #
    @8
    @5
    cA
    elin
    @0
    @2
    @9
    @10
    @11
    @0
    @9
    @2
    @10
    @11
    wi
    #
    @0
    @9
    @8
    vz
    cv
    #
    vw
    cv
    #
    cva
    co
    #
    wceq
    #
    vw
    @4
    wrex
    vz
    cB
    wrex
    #
    @2
    @12
    wi
    #
    @0
    cB
    csh
    wcel
    #
    @4
    csh
    wcel
    #
    @9
    @17
    wb
    cB
    sumdmdi.2
    chshii
    #
    cC
    spansnsh
    #
    vz
    vw
    cB
    @4
    @8
    shsel
    sylancr
    @0
    @16
    @18
    vz
    vw
    cB
    @4
    @0
    @13
    cB
    wcel
    #
    @14
    @4
    wcel
    #
    wa
    #
    @16
    @18
    @10
    @0
    @25
    @16
    wa
    #
    @2
    @11
    @10
    @26
    @0
    @2
    @11
    wi
    @10
    @26
    @0
    @2
    @11
    @10
    @23
    @24
    @16
    @3
    @11
    wi
    #
    @16
    @10
    @23
    @24
    @27
    @16
    @10
    @23
    @24
    @27
    wi
    @16
    @10
    @23
    wa
    #
    wa
    #
    @3
    @24
    @11
    @29
    @3
    @24
    @11
    wi
    @29
    @3
    wa
    #
    @24
    @14
    c0v
    wceq
    #
    @11
    @30
    @24
    @14
    @1
    wcel
    #
    @31
    @29
    @0
    @24
    @32
    wi
    #
    @2
    @16
    @28
    @0
    @33
    @28
    @0
    @24
    @16
    @32
    @28
    @0
    @24
    @16
    @32
    wi
    @28
    @0
    @24
    wa
    #
    wa
    @16
    @8
    @13
    cmv
    co
    #
    @14
    wceq
    #
    @32
    @10
    @23
    @34
    @36
    @16
    wb
    #
    @10
    @8
    chil
    wcel
    #
    @23
    @13
    chil
    wcel
    #
    @34
    @14
    chil
    wcel
    #
    @37
    @8
    cA
    sumdmdi.1
    cheli
    @13
    cB
    sumdmdi.2
    cheli
    #
    cC
    @14
    elspansncl
    @38
    @39
    @40
    w3a
    @36
    @15
    @8
    wceq
    @16
    @8
    @13
    @14
    hvsubadd
    @15
    @8
    eqcom
    syl6bb
    syl3an
    3expa
    @28
    @36
    @32
    wi
    @34
    @28
    @35
    @1
    wcel
    @36
    @32
    cA
    cB
    @8
    @13
    cA
    sumdmdi.1
    chshii
    #
    @21
    shsvsi
    @35
    @14
    @1
    eleq1
    syl5ibcom
    adantr
    sylbird
    exp32
    com4r
    imp31
    adantrr
    @3
    @24
    @32
    @31
    wi
    wi
    @29
    @3
    @24
    @32
    @31
    @1
    csh
    wcel
    @3
    @24
    @32
    wa
    wa
    @31
    wi
    cA
    cB
    @42
    @21
    shscli
    @1
    cC
    @14
    elspansn5
    ax-mp
    exp32
    adantl
    mpdd
    @29
    @24
    @31
    @11
    wi
    #
    wi
    @3
    @29
    @43
    @24
    @16
    @28
    @31
    @11
    @16
    @28
    @31
    wa
    #
    wa
    @8
    @13
    wceq
    #
    @11
    @44
    @16
    @45
    @23
    @31
    @16
    @45
    wb
    @10
    @23
    @31
    wa
    @15
    @13
    @8
    @23
    @39
    @31
    @15
    @13
    wceq
    @41
    @31
    @39
    @15
    @13
    c0v
    cva
    co
    @13
    @14
    c0v
    @13
    cva
    oveq2
    @13
    ax-hvaddid
    sylan9eqr
    sylan
    eqeq2d
    adantll
    biimpac
    @28
    @45
    @11
    wi
    @16
    @31
    @10
    @23
    @45
    @11
    @23
    @45
    wa
    @10
    @8
    cB
    wcel
    #
    @11
    @45
    @46
    @23
    @8
    @13
    cB
    eleq1
    biimparc
    @46
    @10
    @11
    @11
    @46
    @10
    wa
    @8
    cB
    cA
    elin
    biimpri
    ancoms
    sylan2
    expr
    ad2antrl
    mpd
    expr
    a1d
    adantr
    mpdd
    ex
    com23
    exp32
    com4l
    imp4c
    exp4a
    com23
    com4l
    expd
    rexlimdvv
    sylbid
    com23
    imp4b
    syl5bi
    ssrdv
    @0
    @7
    @6
    wss
    #
    @2
    @0
    cB
    @5
    wss
    #
    @47
    @0
    @19
    @20
    @48
    @21
    @22
    cB
    @4
    shsub1
    sylancr
    cB
    @5
    cA
    ssrin
    syl
    adantr
    eqssd
end
