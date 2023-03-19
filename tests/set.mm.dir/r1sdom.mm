include "con0.mm"
include "wcel.mm"
include "cr1.mm"
include "cfv.mm"
include "csdm.mm"
include "wbr.mm"
include "cv.mm"
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
include "wo.mm"
include "elsuci.mm"
include "sdomtr.mm"
include "expcom.mm"
include "cpw.mm"
include "fvex.mm"
include "canth2.mm"
include "r1suc.mm"
include "syl5breqr.mm"
include "syl11.mm"
include "imim2i.mm"
include "breq1d.mm"
include "syl5ibr.mm"
include "a1i.mm"
include "jaod.mm"
include "syl5.mm"
include "com3r.mm"
include "wlim.mm"
include "wral.mm"
include "wrex.mm"
include "cuni.mm"
include "limuni.mm"
include "eleq2d.mm"
include "eluni2.mm"
include "syl6bb.mm"
include "wa.mm"
include "r19.29.mm"
include "cdom.mm"
include "cvv.mm"
include "wss.mm"
include "ciun.mm"
include "ssiun2.mm"
include "vex.mm"
include "r1lim.mm"
include "mpan.mm"
include "sseq2d.mm"
include "ssdomg.mm"
include "sylsyld.mm"
include "id.mm"
include "imp.mm"
include "sdomdomtr.mm"
include "syl6.mm"
include "rexlimdv.mm"
include "expcomd.mm"
include "sylbid.mm"
include "com23.mm"
include "tfinds.mm"

theorem r1sdom
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. On /\ B e. A ) -> ( R1 ` B ) ~< ( R1 ` A ) )

  proof
    cA
    con0
    wcel
    cB
    cA
    wcel
    #
    cB
    cr1
    cfv
    #
    cA
    cr1
    cfv
    #
    csdm
    wbr
    #
    cB
    vx
    cv
    #
    wcel
    #
    @1
    @4
    cr1
    cfv
    #
    csdm
    wbr
    #
    wi
    cB
    c0
    wcel
    #
    @1
    c0
    cr1
    cfv
    #
    csdm
    wbr
    #
    wi
    cB
    vy
    cv
    #
    wcel
    #
    @1
    @11
    cr1
    cfv
    #
    csdm
    wbr
    #
    wi
    #
    cB
    @11
    csuc
    #
    wcel
    #
    @1
    @16
    cr1
    cfv
    #
    csdm
    wbr
    #
    wi
    @0
    @3
    wi
    vx
    vy
    cA
    @4
    c0
    wceq
    #
    @5
    @8
    @7
    @10
    @4
    c0
    cB
    eleq2
    @20
    @6
    @9
    @1
    csdm
    @4
    c0
    cr1
    fveq2
    breq2d
    imbi12d
    @4
    @11
    wceq
    #
    @5
    @12
    @7
    @14
    @4
    @11
    cB
    eleq2
    @21
    @6
    @13
    @1
    csdm
    @4
    @11
    cr1
    fveq2
    breq2d
    imbi12d
    @4
    @16
    wceq
    #
    @5
    @17
    @7
    @19
    @4
    @16
    cB
    eleq2
    @22
    @6
    @18
    @1
    csdm
    @4
    @16
    cr1
    fveq2
    breq2d
    imbi12d
    @4
    cA
    wceq
    #
    @5
    @0
    @7
    @3
    @4
    cA
    cB
    eleq2
    @23
    @6
    @2
    @1
    csdm
    @4
    cA
    cr1
    fveq2
    breq2d
    imbi12d
    @8
    @10
    cB
    noel
    pm2.21i
    @15
    @17
    @11
    con0
    wcel
    #
    @19
    @17
    @12
    cB
    @11
    wceq
    #
    wo
    @15
    @24
    @19
    wi
    #
    cB
    @11
    elsuci
    @15
    @12
    @26
    @25
    @14
    @26
    @12
    @13
    @18
    csdm
    wbr
    #
    @14
    @19
    @24
    @14
    @27
    @19
    @1
    @13
    @18
    sdomtr
    expcom
    @24
    @13
    @13
    cpw
    @18
    csdm
    @13
    @11
    cr1
    fvex
    canth2
    @11
    r1suc
    syl5breqr
    #
    syl11
    imim2i
    @25
    @26
    wi
    @15
    @24
    @19
    @25
    @27
    @28
    @25
    @1
    @13
    @18
    csdm
    cB
    @11
    cr1
    fveq2
    breq1d
    syl5ibr
    a1i
    jaod
    syl5
    com3r
    @4
    wlim
    #
    @5
    @15
    vy
    @4
    wral
    #
    @7
    @29
    @5
    @12
    vy
    @4
    wrex
    #
    @30
    @7
    wi
    @29
    @5
    cB
    @4
    cuni
    #
    wcel
    @31
    @29
    @4
    @32
    cB
    @4
    limuni
    eleq2d
    vy
    cB
    @4
    eluni2
    syl6bb
    @29
    @30
    @31
    @7
    @30
    @31
    wa
    @15
    @12
    wa
    #
    vy
    @4
    wrex
    @29
    @7
    @15
    @12
    vy
    @4
    r19.29
    @29
    @33
    @7
    vy
    @4
    @29
    @11
    @4
    wcel
    #
    @13
    @6
    cdom
    wbr
    #
    @33
    @7
    wi
    @29
    @6
    cvv
    wcel
    #
    @34
    @13
    @6
    wss
    #
    @35
    @36
    @29
    @4
    cr1
    fvex
    a1i
    @34
    @37
    @29
    @13
    vy
    @4
    @13
    ciun
    #
    wss
    vy
    @4
    @13
    ssiun2
    @29
    @6
    @38
    @13
    @4
    cvv
    wcel
    @29
    @6
    @38
    wceq
    vx
    vex
    vy
    @4
    cvv
    r1lim
    mpan
    sseq2d
    syl5ibr
    @13
    @6
    cvv
    ssdomg
    sylsyld
    @33
    @14
    @35
    @7
    @15
    @12
    @14
    @15
    id
    imp
    @14
    @35
    @7
    @1
    @13
    @6
    sdomdomtr
    expcom
    syl5
    syl6
    rexlimdv
    syl5
    expcomd
    sylbid
    com23
    tfinds
    imp
end
