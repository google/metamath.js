include "cfn.mm"
include "wcel.mm"
include "cxp.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "xpeq1.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "0xp.mm"
include "0fin.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wral.mm"
include "wa.mm"
include "wn.mm"
include "wex.mm"
include "neq0.mm"
include "sneq.mm"
include "difeq2d.mm"
include "xpeq1d.mm"
include "rspcv.mm"
include "adantl.mm"
include "pm2.27.mm"
include "ad2antlr.mm"
include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "c2nd.mm"
include "cres.mm"
include "wf1o.mm"
include "snex.mm"
include "xpexg.mm"
include "mpan.mm"
include "id.mm"
include "vex.mm"
include "2ndconst.mm"
include "mp1i.mm"
include "f1oen2g.mm"
include "syl3anc.mm"
include "enfii.mm"
include "mpdan.mm"
include "cun.mm"
include "unfi.mm"
include "xpundir.mm"
include "difsnid.mm"
include "syl5eqr.mm"
include "biimpd.mm"
include "syl5.mm"
include "mpan2d.mm"
include "3syld.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "syl6eqel.mm"
include "a1d.mm"
include "pm2.61d2.mm"
include "com23.mm"
include "findcard.mm"
include "imp.mm"

theorem xpfi
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. Fin /\ B e. Fin ) -> ( A X. B ) e. Fin )

  proof
    cA
    cfn
    wcel
    cB
    cfn
    wcel
    #
    cA
    cB
    cxp
    #
    cfn
    wcel
    #
    @0
    vx
    cv
    #
    cB
    cxp
    #
    cfn
    wcel
    #
    wi
    @0
    c0
    cB
    cxp
    #
    cfn
    wcel
    #
    wi
    @0
    vy
    cv
    #
    vz
    cv
    #
    csn
    #
    cdif
    #
    cB
    cxp
    #
    cfn
    wcel
    #
    wi
    #
    @0
    @8
    cB
    cxp
    #
    cfn
    wcel
    #
    wi
    @0
    @2
    wi
    vx
    vy
    vz
    cA
    @3
    c0
    wceq
    #
    @5
    @7
    @0
    @17
    @4
    @6
    cfn
    @3
    c0
    cB
    xpeq1
    eleq1d
    imbi2d
    @3
    @11
    wceq
    #
    @5
    @13
    @0
    @18
    @4
    @12
    cfn
    @3
    @11
    cB
    xpeq1
    eleq1d
    imbi2d
    @3
    @8
    wceq
    #
    @5
    @16
    @0
    @19
    @4
    @15
    cfn
    @3
    @8
    cB
    xpeq1
    eleq1d
    imbi2d
    @3
    cA
    wceq
    #
    @5
    @2
    @0
    @20
    @4
    @1
    cfn
    @3
    cA
    cB
    xpeq1
    eleq1d
    imbi2d
    @7
    @0
    @6
    c0
    cfn
    cB
    0xp
    0fin
    eqeltri
    #
    a1i
    @8
    cfn
    wcel
    #
    @0
    @14
    vz
    @8
    wral
    #
    @16
    @22
    @0
    @23
    @16
    wi
    #
    @22
    @0
    wa
    #
    @8
    c0
    wceq
    #
    @24
    @26
    wn
    vw
    cv
    #
    @8
    wcel
    #
    vw
    wex
    @25
    @24
    vw
    @8
    neq0
    @25
    @28
    @24
    vw
    @25
    @28
    @24
    @25
    @28
    wa
    #
    @23
    @0
    @8
    @27
    csn
    #
    cdif
    #
    cB
    cxp
    #
    cfn
    wcel
    #
    wi
    #
    @33
    @16
    @28
    @23
    @34
    wi
    @25
    @14
    @34
    vz
    @27
    @8
    @9
    @27
    wceq
    #
    @13
    @33
    @0
    @35
    @12
    @32
    cfn
    @35
    @11
    @31
    cB
    @35
    @10
    @30
    @8
    @9
    @27
    sneq
    difeq2d
    xpeq1d
    eleq1d
    imbi2d
    rspcv
    adantl
    @0
    @34
    @33
    wi
    @22
    @28
    @0
    @33
    pm2.27
    ad2antlr
    @29
    @33
    @30
    cB
    cxp
    #
    cfn
    wcel
    #
    @16
    @0
    @37
    @22
    @28
    @0
    @36
    cB
    cen
    wbr
    #
    @37
    @0
    @36
    cvv
    wcel
    #
    @0
    @36
    cB
    c2nd
    @36
    cres
    #
    wf1o
    #
    @38
    @30
    cvv
    wcel
    @0
    @39
    @27
    snex
    @30
    cB
    cvv
    cfn
    xpexg
    mpan
    @0
    id
    @27
    cvv
    wcel
    @41
    @0
    vw
    vex
    @27
    cB
    cvv
    2ndconst
    mp1i
    @36
    cB
    @40
    cvv
    cfn
    f1oen2g
    syl3anc
    @36
    cB
    enfii
    mpdan
    ad2antlr
    @33
    @37
    wa
    @32
    @36
    cun
    #
    cfn
    wcel
    #
    @29
    @16
    @32
    @36
    unfi
    @28
    @43
    @16
    wi
    @25
    @28
    @43
    @16
    @28
    @42
    @15
    cfn
    @28
    @42
    @31
    @30
    cun
    #
    cB
    cxp
    @15
    @31
    @30
    cB
    xpundir
    @28
    @44
    @8
    cB
    @8
    @27
    difsnid
    xpeq1d
    syl5eqr
    eleq1d
    biimpd
    adantl
    syl5
    mpan2d
    3syld
    ex
    exlimdv
    syl5bi
    @26
    @16
    @23
    @26
    @15
    @6
    cfn
    @8
    c0
    cB
    xpeq1
    @21
    syl6eqel
    a1d
    pm2.61d2
    ex
    com23
    findcard
    imp
end
