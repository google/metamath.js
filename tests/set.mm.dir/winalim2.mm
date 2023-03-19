include "cwina.mm"
include "wcel.mm"
include "com.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cale.mm"
include "cfv.mm"
include "wceq.mm"
include "con0.mm"
include "wrex.mm"
include "wlim.mm"
include "wex.mm"
include "ccrd.mm"
include "winacard.mm"
include "wss.mm"
include "wb.mm"
include "winainf.mm"
include "cardalephex.mm"
include "syl.mm"
include "mpbid.mm"
include "adantr.mm"
include "df-rex.mm"
include "simprr.mm"
include "eqcomd.mm"
include "c0.mm"
include "csuc.mm"
include "cvv.mm"
include "w3o.mm"
include "simprl.mm"
include "onzsl.mm"
include "sylib.mm"
include "wn.mm"
include "simplr.mm"
include "fveq2.mm"
include "aleph0.mm"
include "syl6eq.mm"
include "eqtr.mm"
include "sylan2.mm"
include "ex.mm"
include "necon3ad.mm"
include "sylc.mm"
include "pm2.21d.mm"
include "csdm.mm"
include "wbr.mm"
include "wral.mm"
include "suceloni.mm"
include "vex.mm"
include "sucid.mm"
include "alephord2i.mm"
include "mpisyl.mm"
include "ad2antrl.mm"
include "simplrr.mm"
include "ad2antll.mm"
include "eqtrd.mm"
include "eleqtrrd.mm"
include "ccf.mm"
include "elwina.mm"
include "simp3bi.mm"
include "ad3antrrr.mm"
include "breq1.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "expr.mm"
include "wi.mm"
include "iscard.mm"
include "simprbi.mm"
include "rsp.mm"
include "3syl.mm"
include "breq2d.mm"
include "sylibd.mm"
include "alephnbtwn2.mm"
include "pm3.21.mm"
include "mtoi.mm"
include "syl6.mm"
include "imp.mm"
include "nrexdv.mm"
include "pm2.65d.mm"
include "simpr.mm"
include "a1i.mm"
include "3jaod.mm"
include "mpd.mm"
include "jca.mm"
include "eximdv.mm"
include "syl5bi.mm"

theorem winalim2
  let vx: setvar x
  let cA: class A
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( ( A e. InaccW /\ A =/= _om ) -> E. x ( ( aleph ` x ) = A /\ Lim x ) )

  proof
    cA
    cwina
    wcel
    #
    cA
    com
    wne
    #
    wa
    #
    cA
    vx
    cv
    #
    cale
    cfv
    #
    wceq
    #
    vx
    con0
    wrex
    #
    @4
    cA
    wceq
    #
    @3
    wlim
    #
    wa
    #
    vx
    wex
    #
    @0
    @6
    @1
    @0
    cA
    ccrd
    cfv
    cA
    wceq
    #
    @6
    cA
    winacard
    #
    @0
    com
    cA
    wss
    @11
    @6
    wb
    cA
    winainf
    vx
    cA
    cardalephex
    syl
    mpbid
    adantr
    @6
    @3
    con0
    wcel
    #
    @5
    wa
    #
    vx
    wex
    @2
    @10
    @5
    vx
    con0
    df-rex
    @2
    @14
    @9
    vx
    @2
    @14
    @9
    @2
    @14
    wa
    #
    @7
    @8
    @15
    cA
    @4
    @2
    @13
    @5
    simprr
    #
    eqcomd
    @15
    @3
    c0
    wceq
    #
    @3
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
    @3
    cvv
    wcel
    #
    @8
    wa
    #
    w3o
    #
    @8
    @15
    @13
    @24
    @2
    @13
    @5
    simprl
    vy
    @3
    onzsl
    sylib
    @15
    @17
    @8
    @21
    @23
    @15
    @17
    @8
    @15
    @5
    @1
    @17
    wn
    @16
    @0
    @1
    @14
    simplr
    @5
    @17
    cA
    com
    @5
    @17
    cA
    com
    wceq
    #
    @17
    @5
    @4
    com
    wceq
    @25
    @17
    @4
    c0
    cale
    cfv
    com
    @3
    c0
    cale
    fveq2
    aleph0
    syl6eq
    cA
    @4
    com
    eqtr
    sylan2
    ex
    necon3ad
    sylc
    pm2.21d
    @15
    @21
    @8
    @15
    @20
    vy
    con0
    @15
    @18
    con0
    wcel
    #
    wa
    @20
    @18
    cale
    cfv
    #
    vw
    cv
    #
    csdm
    wbr
    #
    vw
    cA
    wrex
    #
    @15
    @26
    @20
    @30
    @15
    @26
    @20
    wa
    #
    wa
    #
    @27
    cA
    wcel
    vz
    cv
    #
    @28
    csdm
    wbr
    #
    vw
    cA
    wrex
    #
    vz
    cA
    wral
    #
    @30
    @32
    @27
    @19
    cale
    cfv
    #
    cA
    @26
    @27
    @37
    wcel
    #
    @15
    @20
    @26
    @19
    con0
    wcel
    @18
    @19
    wcel
    @38
    @18
    suceloni
    @18
    vy
    vex
    sucid
    @18
    @19
    alephord2i
    mpisyl
    ad2antrl
    @32
    cA
    @4
    @37
    @2
    @13
    @5
    @31
    simplrr
    @20
    @4
    @37
    wceq
    @15
    @26
    @3
    @19
    cale
    fveq2
    ad2antll
    eqtrd
    #
    eleqtrrd
    @0
    @36
    @1
    @14
    @31
    @0
    cA
    c0
    wne
    cA
    ccf
    cfv
    cA
    wceq
    @36
    vz
    vw
    cA
    elwina
    simp3bi
    ad3antrrr
    @35
    @30
    vz
    @27
    cA
    @33
    @27
    wceq
    @34
    @29
    vw
    cA
    @33
    @27
    @28
    csdm
    breq1
    rexbidv
    rspcva
    syl2anc
    expr
    @15
    @26
    @20
    @30
    wn
    @32
    @29
    vw
    cA
    @32
    @28
    cA
    wcel
    #
    @29
    wn
    #
    @32
    @40
    @28
    @37
    csdm
    wbr
    #
    @41
    @32
    @40
    @28
    cA
    csdm
    wbr
    #
    @42
    @0
    @40
    @43
    wi
    #
    @1
    @14
    @31
    @0
    @11
    @43
    vw
    cA
    wral
    #
    @44
    @12
    @11
    cA
    con0
    wcel
    @45
    vw
    cA
    iscard
    simprbi
    @43
    vw
    cA
    rsp
    3syl
    ad3antrrr
    @32
    cA
    @37
    @28
    csdm
    @39
    breq2d
    sylibd
    @42
    @29
    @29
    @42
    wa
    @18
    @28
    alephnbtwn2
    @42
    @29
    pm3.21
    mtoi
    syl6
    imp
    nrexdv
    expr
    pm2.65d
    nrexdv
    pm2.21d
    @23
    @8
    wi
    @15
    @22
    @8
    simpr
    a1i
    3jaod
    mpd
    jca
    ex
    eximdv
    syl5bi
    mpd
end
