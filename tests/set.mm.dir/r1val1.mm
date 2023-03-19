include "cr1.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cpw.mm"
include "ciun.mm"
include "c0.mm"
include "wceq.mm"
include "wss.mm"
include "csuc.mm"
include "con0.mm"
include "wrex.mm"
include "cvv.mm"
include "wlim.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "r10.mm"
include "syl6eq.mm"
include "0ss.mm"
include "a1i.mm"
include "eqsstrd.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nfss.mm"
include "wi.mm"
include "eleq1.mm"
include "biimpac.mm"
include "wb.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limsuc.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "r1sucg.mm"
include "syl.mm"
include "eqtrd.mm"
include "vex.mm"
include "sucid.mm"
include "syl5eleqr.mm"
include "ssiun2.mm"
include "ex.mm"
include "a1d.mm"
include "rexlimd.mm"
include "imp.mm"
include "r1limg.mm"
include "wral.mm"
include "wtr.mm"
include "r1tr.mm"
include "dftr4.mm"
include "mpbi.mm"
include "ralrimivw.mm"
include "ss2iun.mm"
include "adantrl.mm"
include "w3o.mm"
include "word.mm"
include "limord.mm"
include "ordsson.mm"
include "sseli.mm"
include "onzsl.mm"
include "sylib.mm"
include "mpjao3dan.mm"
include "ordtr1.mm"
include "ancoms.mm"
include "ordelord.mm"
include "mpan.mm"
include "adantr.mm"
include "ordelsuc.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simpl.mm"
include "r1ord3g.mm"
include "mpd.mm"
include "eqsstr3d.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "eqssd.mm"

theorem r1val1
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. dom R1 -> ( R1 ` A ) = U_ x e. A ~P ( R1 ` x ) )

  proof
    cA
    cr1
    cdm
    #
    wcel
    #
    cA
    cr1
    cfv
    #
    vx
    cA
    vx
    cv
    #
    cr1
    cfv
    #
    cpw
    #
    ciun
    #
    @1
    cA
    c0
    wceq
    #
    @2
    @6
    wss
    #
    cA
    @3
    csuc
    #
    wceq
    #
    vx
    con0
    wrex
    #
    cA
    cvv
    wcel
    #
    cA
    wlim
    #
    wa
    #
    @1
    @7
    wa
    #
    @2
    c0
    @6
    @15
    @2
    c0
    cr1
    cfv
    c0
    @15
    cA
    c0
    cr1
    @1
    @7
    simpr
    fveq2d
    r10
    syl6eq
    c0
    @6
    wss
    @15
    @6
    0ss
    a1i
    eqsstrd
    @1
    @11
    @8
    @1
    @10
    @8
    vx
    con0
    @1
    vx
    nfv
    vx
    @2
    @6
    vx
    @2
    nfcv
    vx
    cA
    @5
    nfiu1
    nfss
    @1
    @10
    @8
    wi
    @3
    con0
    wcel
    @1
    @10
    @8
    @1
    @10
    wa
    #
    @2
    @5
    @6
    @16
    @2
    @9
    cr1
    cfv
    #
    @5
    @16
    cA
    @9
    cr1
    @1
    @10
    simpr
    #
    fveq2d
    @16
    @3
    @0
    wcel
    #
    @17
    @5
    wceq
    #
    @16
    @9
    @0
    wcel
    #
    @19
    @10
    @1
    @21
    cA
    @9
    @0
    eleq1
    biimpac
    @0
    wlim
    #
    @19
    @21
    wb
    cr1
    wfun
    @22
    r1funlim
    simpri
    #
    @0
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
    @16
    @3
    cA
    wcel
    #
    @5
    @6
    wss
    @16
    @3
    @9
    cA
    @3
    vx
    vex
    sucid
    @18
    syl5eleqr
    vx
    cA
    @5
    ssiun2
    syl
    eqsstrd
    ex
    a1d
    rexlimd
    imp
    @1
    @13
    @8
    @12
    @1
    @13
    wa
    #
    @2
    vx
    cA
    @4
    ciun
    #
    @6
    vx
    cA
    r1limg
    @27
    @4
    @5
    wss
    #
    vx
    cA
    wral
    @28
    @6
    wss
    @27
    @29
    vx
    cA
    @29
    @27
    @4
    wtr
    @29
    @3
    r1tr
    @4
    dftr4
    mpbi
    a1i
    ralrimivw
    vx
    cA
    @4
    @5
    ss2iun
    syl
    eqsstrd
    adantrl
    @1
    cA
    con0
    wcel
    @7
    @11
    @14
    w3o
    @0
    con0
    cA
    @0
    word
    #
    @0
    con0
    wss
    @22
    @30
    @23
    @0
    limord
    ax-mp
    #
    @0
    ordsson
    ax-mp
    sseli
    vx
    cA
    onzsl
    sylib
    mpjao3dan
    @1
    @5
    @2
    wss
    #
    vx
    cA
    wral
    @6
    @2
    wss
    @1
    @32
    vx
    cA
    @1
    @26
    wa
    #
    @5
    @17
    @2
    @33
    @19
    @20
    @26
    @1
    @19
    @30
    @26
    @1
    wa
    @19
    wi
    @31
    @3
    cA
    @0
    ordtr1
    ax-mp
    ancoms
    #
    @25
    syl
    @33
    @9
    cA
    wss
    #
    @17
    @2
    wss
    #
    @33
    @26
    @35
    @1
    @26
    simpr
    #
    @33
    @26
    cA
    word
    #
    @26
    @35
    wb
    @37
    @1
    @38
    @26
    @30
    @1
    @38
    @31
    @0
    cA
    ordelord
    mpan
    adantr
    @3
    cA
    cA
    ordelsuc
    syl2anc
    mpbid
    @33
    @21
    @1
    @35
    @36
    wi
    @33
    @19
    @21
    @34
    @24
    sylib
    @1
    @26
    simpl
    @9
    cA
    r1ord3g
    syl2anc
    mpd
    eqsstr3d
    ralrimiva
    vx
    cA
    @5
    @2
    iunss
    sylibr
    eqssd
end
