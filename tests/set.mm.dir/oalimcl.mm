include "con0.mm"
include "wcel.mm"
include "wlim.mm"
include "wa.mm"
include "coa.mm"
include "co.mm"
include "word.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "csuc.mm"
include "wrex.mm"
include "wo.mm"
include "wn.mm"
include "limelon.mm"
include "oacl.mm"
include "eloni.mm"
include "syl.mm"
include "sylan2.mm"
include "0ellim.mm"
include "n0i.mm"
include "ad2antll.mm"
include "wi.mm"
include "oa00.mm"
include "simpr.mm"
include "syl6bi.mm"
include "con3d.mm"
include "mpd.mm"
include "ciun.mm"
include "vex.mm"
include "sucid.mm"
include "oalim.mm"
include "eqeq1.mm"
include "syl5ib.mm"
include "imp.mm"
include "syl5eleq.mm"
include "eliun.mm"
include "sylib.mm"
include "onelon.mm"
include "sylan.mm"
include "onnbtwn.mm"
include "imnan.mm"
include "sylibr.mm"
include "com12.mm"
include "adantl.mm"
include "ad2antrl.mm"
include "wb.mm"
include "ordsucelsuc.mm"
include "3syl.mm"
include "oasuc.mm"
include "eleq2d.mm"
include "bitr4d.mm"
include "eleq1.mm"
include "bicomd.mm"
include "sylan9bbr.mm"
include "adantr.mm"
include "sucelon.mm"
include "jca.mm"
include "oaord.mm"
include "3expa.mm"
include "ancoms.mm"
include "biimpd.mm"
include "exp32.mm"
include "com4l.mm"
include "imp32.mm"
include "mtod.mm"
include "exp44.mm"
include "rexlimdv.mm"
include "expcom.mm"
include "pm2.01d.mm"
include "nrexdv.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "dflim3.mm"

theorem oalimcl
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. On /\ ( B e. C /\ Lim B ) ) -> Lim ( A +o B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    cC
    wcel
    #
    cB
    wlim
    #
    wa
    #
    wa
    #
    cA
    cB
    coa
    co
    #
    word
    #
    @5
    c0
    wceq
    #
    @5
    vy
    cv
    #
    csuc
    #
    wceq
    #
    vy
    con0
    wrex
    #
    wo
    wn
    #
    @5
    wlim
    @3
    @0
    cB
    con0
    wcel
    #
    @6
    cB
    cC
    limelon
    #
    @0
    @13
    wa
    #
    @5
    con0
    wcel
    @6
    cA
    cB
    oacl
    @5
    eloni
    syl
    sylan2
    @4
    @7
    wn
    #
    @11
    wn
    @12
    @4
    cB
    c0
    wceq
    #
    wn
    #
    @16
    @2
    @18
    @0
    @1
    @2
    c0
    cB
    wcel
    @18
    cB
    0ellim
    cB
    c0
    n0i
    syl
    ad2antll
    @3
    @0
    @13
    @18
    @16
    wi
    @14
    @15
    @7
    @17
    @15
    @7
    cA
    c0
    wceq
    #
    @17
    wa
    @17
    cA
    cB
    oa00
    @19
    @17
    simpr
    syl6bi
    con3d
    sylan2
    mpd
    @4
    @10
    vy
    con0
    @4
    @10
    wn
    #
    @8
    con0
    wcel
    @4
    @10
    @10
    @4
    @20
    @10
    @4
    wa
    #
    @8
    cA
    vx
    cv
    #
    coa
    co
    #
    wcel
    #
    vx
    cB
    wrex
    #
    @20
    @21
    @8
    vx
    cB
    @23
    ciun
    #
    wcel
    @25
    @21
    @8
    @9
    @26
    @8
    vy
    vex
    sucid
    @10
    @4
    @9
    @26
    wceq
    #
    @4
    @5
    @26
    wceq
    @10
    @27
    vx
    cA
    cB
    cC
    oalim
    @5
    @9
    @26
    eqeq1
    syl5ib
    imp
    syl5eleq
    vx
    @8
    cB
    @23
    eliun
    sylib
    @4
    @25
    @20
    wi
    @10
    @4
    @24
    @20
    vx
    cB
    @0
    @3
    @22
    cB
    wcel
    #
    @24
    @20
    wi
    wi
    @0
    @3
    @28
    @24
    @20
    @0
    @3
    @28
    wa
    #
    @24
    wa
    wa
    @10
    cB
    @22
    csuc
    #
    wcel
    #
    @29
    @31
    wn
    #
    @0
    @24
    @29
    @22
    con0
    wcel
    #
    @32
    @3
    @13
    @28
    @33
    @14
    cB
    @22
    onelon
    sylan
    #
    @28
    @33
    @32
    wi
    @3
    @33
    @28
    @32
    @33
    @28
    @31
    wa
    wn
    @28
    @32
    wi
    @22
    cB
    onnbtwn
    @28
    @31
    imnan
    sylibr
    com12
    adantl
    mpd
    ad2antrl
    @0
    @29
    @24
    @10
    @31
    wi
    @10
    @0
    @29
    @24
    @31
    @10
    @0
    @29
    @24
    @31
    wi
    @10
    @0
    @29
    wa
    #
    wa
    #
    @24
    @31
    @36
    @24
    @5
    cA
    @30
    coa
    co
    #
    wcel
    #
    @31
    @35
    @24
    @9
    @37
    wcel
    #
    @10
    @38
    @29
    @0
    @33
    @24
    @39
    wb
    @34
    @0
    @33
    wa
    #
    @24
    @9
    @23
    csuc
    #
    wcel
    #
    @39
    @40
    @23
    con0
    wcel
    @23
    word
    @24
    @42
    wb
    cA
    @22
    oacl
    @23
    eloni
    @8
    @23
    ordsucelsuc
    3syl
    @40
    @37
    @41
    @9
    cA
    @22
    oasuc
    eleq2d
    bitr4d
    sylan2
    @10
    @38
    @39
    @5
    @9
    @37
    eleq1
    bicomd
    sylan9bbr
    @35
    @31
    @38
    wb
    #
    @10
    @29
    @0
    @43
    @29
    @13
    @30
    con0
    wcel
    #
    wa
    @0
    @43
    @29
    @13
    @44
    @3
    @13
    @28
    @14
    adantr
    @29
    @33
    @44
    @34
    @22
    sucelon
    sylib
    jca
    @13
    @44
    @0
    @43
    cB
    @30
    cA
    oaord
    3expa
    sylan
    ancoms
    adantl
    bitr4d
    biimpd
    exp32
    com4l
    imp32
    mtod
    exp44
    imp
    rexlimdv
    adantl
    mpd
    expcom
    pm2.01d
    adantr
    nrexdv
    @7
    @11
    ioran
    sylanbrc
    vy
    @5
    dflim3
    sylanbrc
end
