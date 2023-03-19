include "cr1.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "csuc.mm"
include "con0.mm"
include "wrex.mm"
include "cvv.mm"
include "wlim.mm"
include "wa.mm"
include "w3o.mm"
include "cpw.mm"
include "wss.mm"
include "cdm.mm"
include "word.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limord.mm"
include "ax-mp.mm"
include "ordsson.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "onzsl.mm"
include "sylib.mm"
include "noel.mm"
include "fveq2.mm"
include "r10.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "mtoi.mm"
include "pm2.21d.mm"
include "simpl.mm"
include "simpr.mm"
include "fveq2d.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "wb.mm"
include "limsuc.mm"
include "sylibr.mm"
include "r1sucg.mm"
include "syl.mm"
include "eqtrd.mm"
include "eleqtrd.mm"
include "elpwi.mm"
include "sspwb.mm"
include "sseqtr4d.mm"
include "ex.mm"
include "rexlimdvw.mm"
include "wtr.mm"
include "r1tr.mm"
include "ciun.mm"
include "r1limg.mm"
include "sylan.mm"
include "eliun.mm"
include "simprl.mm"
include "ad2antlr.mm"
include "mpbid.mm"
include "simprr.mm"
include "trss.mm"
include "mpsyl.mm"
include "ad2antrr.mm"
include "wi.mm"
include "ordtr1.mm"
include "syl2anc.mm"
include "fvex.mm"
include "elpw2.mm"
include "eleqtrrd.mm"
include "rspcev.mm"
include "rexlimddv.mm"
include "adantld.mm"
include "3jaod.mm"
include "mpd.mm"

theorem r1pwss
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. ( R1 ` B ) -> ~P A C_ ( R1 ` B ) )

  proof
    cA
    cB
    cr1
    cfv
    #
    wcel
    #
    cB
    c0
    wceq
    #
    cB
    vx
    cv
    #
    csuc
    #
    wceq
    #
    vx
    con0
    wrex
    #
    cB
    cvv
    wcel
    #
    cB
    wlim
    #
    wa
    #
    w3o
    #
    cA
    cpw
    #
    @0
    wss
    #
    @1
    cB
    con0
    wcel
    @10
    @1
    cr1
    cdm
    #
    con0
    cB
    @13
    word
    #
    @13
    con0
    wss
    @13
    wlim
    #
    @14
    cr1
    wfun
    @15
    r1funlim
    simpri
    #
    @13
    limord
    ax-mp
    #
    @13
    ordsson
    ax-mp
    cA
    cB
    cr1
    elfvdm
    #
    sseldi
    vx
    cB
    onzsl
    sylib
    @1
    @2
    @12
    @6
    @9
    @1
    @2
    @12
    @1
    @2
    cA
    c0
    wcel
    #
    cA
    noel
    @2
    @1
    @19
    @2
    @0
    c0
    cA
    @2
    @0
    c0
    cr1
    cfv
    c0
    cB
    c0
    cr1
    fveq2
    r10
    syl6eq
    eleq2d
    biimpcd
    mtoi
    pm2.21d
    @1
    @5
    @12
    vx
    con0
    @1
    @5
    @12
    @1
    @5
    wa
    #
    @11
    @3
    cr1
    cfv
    #
    cpw
    #
    @0
    @20
    cA
    @22
    wcel
    #
    @11
    @22
    wss
    #
    @20
    cA
    @0
    @22
    @1
    @5
    simpl
    @20
    @0
    @4
    cr1
    cfv
    #
    @22
    @20
    cB
    @4
    cr1
    @1
    @5
    simpr
    #
    fveq2d
    @20
    @3
    @13
    wcel
    #
    @25
    @22
    wceq
    #
    @20
    @4
    @13
    wcel
    #
    @27
    @20
    cB
    @4
    @13
    @26
    @1
    cB
    @13
    wcel
    #
    @5
    @18
    adantr
    eqeltrrd
    @15
    @27
    @29
    wb
    @16
    @13
    @3
    limsuc
    ax-mp
    #
    sylibr
    @3
    r1sucg
    #
    syl
    eqtrd
    #
    eleqtrd
    @23
    cA
    @21
    wss
    #
    @24
    cA
    @21
    elpwi
    cA
    @21
    sspwb
    #
    sylib
    syl
    @33
    sseqtr4d
    ex
    rexlimdvw
    @1
    @8
    @12
    @7
    @1
    @8
    @12
    @0
    wtr
    @1
    @8
    wa
    #
    @11
    @0
    wcel
    @12
    cB
    r1tr
    @36
    @11
    vy
    cB
    vy
    cv
    #
    cr1
    cfv
    #
    ciun
    #
    @0
    @36
    @11
    @38
    wcel
    #
    vy
    cB
    wrex
    #
    @11
    @39
    wcel
    @36
    cA
    @21
    wcel
    #
    @41
    vx
    cB
    @36
    cA
    vx
    cB
    @21
    ciun
    #
    wcel
    @42
    vx
    cB
    wrex
    @36
    cA
    @0
    @43
    @1
    @8
    simpl
    @1
    @30
    @8
    @0
    @43
    wceq
    @18
    vx
    cB
    r1limg
    sylan
    eleqtrd
    vx
    cA
    cB
    @21
    eliun
    sylib
    @36
    @3
    cB
    wcel
    #
    @42
    wa
    #
    wa
    #
    @4
    csuc
    #
    cB
    wcel
    #
    @11
    @47
    cr1
    cfv
    #
    wcel
    #
    @41
    @46
    @4
    cB
    wcel
    #
    @48
    @46
    @44
    @51
    @36
    @44
    @42
    simprl
    #
    @8
    @44
    @51
    wb
    @1
    @45
    cB
    @3
    limsuc
    ad2antlr
    mpbid
    @8
    @51
    @48
    wb
    @1
    @45
    cB
    @4
    limsuc
    ad2antlr
    mpbid
    @46
    @11
    @25
    cpw
    #
    @49
    @46
    @11
    @25
    wss
    @11
    @53
    wcel
    @46
    @11
    @22
    @25
    @46
    @34
    @24
    @21
    wtr
    @46
    @42
    @34
    @3
    r1tr
    @36
    @44
    @42
    simprr
    @21
    cA
    trss
    mpsyl
    @35
    sylib
    @46
    @27
    @28
    @46
    @44
    @30
    @27
    @52
    @1
    @30
    @8
    @45
    @18
    ad2antrr
    @14
    @44
    @30
    wa
    @27
    wi
    @17
    @3
    cB
    @13
    ordtr1
    ax-mp
    syl2anc
    #
    @32
    syl
    sseqtr4d
    @11
    @25
    @4
    cr1
    fvex
    elpw2
    sylibr
    @46
    @29
    @49
    @53
    wceq
    @46
    @27
    @29
    @54
    @31
    sylib
    @4
    r1sucg
    syl
    eleqtrrd
    @40
    @50
    vy
    @47
    cB
    @37
    @47
    wceq
    @38
    @49
    @11
    @37
    @47
    cr1
    fveq2
    eleq2d
    rspcev
    syl2anc
    rexlimddv
    vy
    @11
    cB
    @38
    eliun
    sylibr
    @1
    @30
    @8
    @0
    @39
    wceq
    @18
    vy
    cB
    r1limg
    sylan
    eleqtrrd
    @0
    @11
    trss
    mpsyl
    ex
    adantld
    3jaod
    mpd
end
