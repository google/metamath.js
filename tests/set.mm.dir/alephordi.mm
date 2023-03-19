include "cv.mm"
include "wcel.mm"
include "cale.mm"
include "cfv.mm"
include "csdm.mm"
include "wbr.mm"
include "wi.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "eleq2.mm"
include "fveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "noel.mm"
include "pm2.21i.mm"
include "con0.mm"
include "wo.mm"
include "vex.mm"
include "elsuc2.mm"
include "alephordilem1.mm"
include "sdomtr.mm"
include "sylan2.mm"
include "expcom.mm"
include "imim2d.mm"
include "com23.mm"
include "breq1d.mm"
include "syl5ibr.mm"
include "a1d.mm"
include "com3r.mm"
include "jaod.mm"
include "syl5bi.mm"
include "wlim.mm"
include "wral.mm"
include "cdom.mm"
include "cen.mm"
include "wn.mm"
include "wa.mm"
include "cvv.mm"
include "wss.mm"
include "fvexd.mm"
include "ciun.mm"
include "ssiun2s.mm"
include "alephlim.mm"
include "mpan.mm"
include "sseq2d.mm"
include "ssdomg.mm"
include "sylsyld.mm"
include "limsuc.mm"
include "sylbid.mm"
include "imp.mm"
include "domnsym.mm"
include "syl.mm"
include "limelon.mm"
include "onelon.mm"
include "sylan.mm"
include "ensym.mm"
include "ensdomtr.mm"
include "ex.mm"
include "syl2im.mm"
include "syl5com.mm"
include "mtod.mm"
include "jcad.mm"
include "brsdom.mm"
include "syl6ibr.mm"
include "tfinds.mm"

theorem alephordi
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y


  assert |- ( B e. On -> ( A e. B -> ( aleph ` A ) ~< ( aleph ` B ) ) )

  proof
    cA
    vx
    cv
    #
    wcel
    #
    cA
    cale
    cfv
    #
    @0
    cale
    cfv
    #
    csdm
    wbr
    #
    wi
    #
    cA
    c0
    wcel
    #
    @2
    c0
    cale
    cfv
    #
    csdm
    wbr
    #
    wi
    cA
    vy
    cv
    #
    wcel
    #
    @2
    @9
    cale
    cfv
    #
    csdm
    wbr
    #
    wi
    #
    cA
    @9
    csuc
    #
    wcel
    #
    @2
    @14
    cale
    cfv
    #
    csdm
    wbr
    #
    wi
    cA
    cB
    wcel
    #
    @2
    cB
    cale
    cfv
    #
    csdm
    wbr
    #
    wi
    vx
    vy
    cB
    @0
    c0
    wceq
    #
    @1
    @6
    @4
    @8
    @0
    c0
    cA
    eleq2
    @21
    @3
    @7
    @2
    csdm
    @0
    c0
    cale
    fveq2
    breq2d
    imbi12d
    @0
    @9
    wceq
    #
    @1
    @10
    @4
    @12
    @0
    @9
    cA
    eleq2
    @22
    @3
    @11
    @2
    csdm
    @0
    @9
    cale
    fveq2
    breq2d
    imbi12d
    @0
    @14
    wceq
    #
    @1
    @15
    @4
    @17
    @0
    @14
    cA
    eleq2
    @23
    @3
    @16
    @2
    csdm
    @0
    @14
    cale
    fveq2
    breq2d
    imbi12d
    @0
    cB
    wceq
    #
    @1
    @18
    @4
    @20
    @0
    cB
    cA
    eleq2
    @24
    @3
    @19
    @2
    csdm
    @0
    cB
    cale
    fveq2
    breq2d
    imbi12d
    @6
    @8
    cA
    noel
    pm2.21i
    @9
    con0
    wcel
    #
    @15
    @13
    @17
    @15
    @10
    cA
    @9
    wceq
    #
    wo
    @25
    @13
    @17
    wi
    #
    @9
    cA
    vy
    vex
    elsuc2
    @25
    @10
    @27
    @26
    @25
    @13
    @10
    @17
    @25
    @12
    @17
    @10
    @12
    @25
    @17
    @25
    @12
    @11
    @16
    csdm
    wbr
    #
    @17
    @9
    alephordilem1
    #
    @2
    @11
    @16
    sdomtr
    sylan2
    expcom
    imim2d
    com23
    @26
    @13
    @25
    @17
    @26
    @25
    @17
    wi
    @13
    @25
    @17
    @26
    @28
    @29
    @26
    @2
    @11
    @16
    csdm
    cA
    @9
    cale
    fveq2
    breq1d
    syl5ibr
    a1d
    com3r
    jaod
    syl5bi
    com23
    @0
    wlim
    #
    @5
    @13
    vy
    @0
    wral
    @30
    @1
    @2
    @3
    cdom
    wbr
    #
    @2
    @3
    cen
    wbr
    #
    wn
    #
    wa
    @4
    @30
    @1
    @31
    @33
    @30
    @3
    cvv
    wcel
    #
    @1
    @2
    @3
    wss
    #
    @31
    @30
    @0
    cale
    fvexd
    #
    @1
    @35
    @30
    @2
    vw
    @0
    vw
    cv
    #
    cale
    cfv
    #
    ciun
    #
    wss
    vw
    @0
    @38
    cA
    @2
    @37
    cA
    cale
    fveq2
    ssiun2s
    @30
    @3
    @39
    @2
    @0
    cvv
    wcel
    #
    @30
    @3
    @39
    wceq
    vx
    vex
    #
    vw
    @0
    cvv
    alephlim
    mpan
    #
    sseq2d
    syl5ibr
    @2
    @3
    cvv
    ssdomg
    sylsyld
    @30
    @1
    @33
    @30
    @1
    wa
    #
    @32
    @3
    cA
    csuc
    #
    cale
    cfv
    #
    csdm
    wbr
    #
    @43
    @45
    @3
    cdom
    wbr
    #
    @46
    wn
    @30
    @1
    @47
    @30
    @1
    @44
    @0
    wcel
    #
    @47
    @0
    cA
    limsuc
    @30
    @34
    @48
    @45
    @3
    wss
    #
    @47
    @36
    @48
    @49
    @30
    @45
    @39
    wss
    vw
    @0
    @38
    @44
    @45
    @37
    @44
    cale
    fveq2
    ssiun2s
    @30
    @3
    @39
    @45
    @42
    sseq2d
    syl5ibr
    @45
    @3
    cvv
    ssdomg
    sylsyld
    sylbid
    imp
    @45
    @3
    domnsym
    syl
    @43
    cA
    con0
    wcel
    #
    @32
    @46
    @30
    @0
    con0
    wcel
    #
    @1
    @50
    @40
    @30
    @51
    @41
    @0
    cvv
    limelon
    mpan
    @0
    cA
    onelon
    sylan
    @32
    @3
    @2
    cen
    wbr
    #
    @50
    @2
    @45
    csdm
    wbr
    #
    @46
    @2
    @3
    ensym
    cA
    alephordilem1
    @52
    @53
    @46
    @3
    @2
    @45
    ensdomtr
    ex
    syl2im
    syl5com
    mtod
    ex
    jcad
    @2
    @3
    brsdom
    syl6ibr
    a1d
    tfinds
end
