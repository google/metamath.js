include "cina.mm"
include "wcel.mm"
include "cv.mm"
include "cpw.mm"
include "cr1.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "wral.mm"
include "cen.mm"
include "wbr.mm"
include "wo.mm"
include "ctsk.mm"
include "cwina.mm"
include "wi.mm"
include "inawina.mm"
include "wrex.mm"
include "ciun.mm"
include "con0.mm"
include "wlim.mm"
include "wceq.mm"
include "winaon.mm"
include "winalim.mm"
include "r1lim.mm"
include "syl2anc.mm"
include "eleq2d.mm"
include "eliun.mm"
include "syl6bb.mm"
include "csuc.mm"
include "wb.mm"
include "onelon.mm"
include "sylan.mm"
include "r1pw.mm"
include "syl.mm"
include "limsuc.mm"
include "r1ord2.mm"
include "sylbid.mm"
include "imp.mm"
include "sseld.mm"
include "rexlimdva.mm"
include "cuni.mm"
include "elssuni.mm"
include "r1tr2.mm"
include "syl6ss.mm"
include "jccil.mm"
include "ralrimiva.mm"
include "crnk.mm"
include "r1suc.mm"
include "rankr1ai.mm"
include "syl6bir.mm"
include "fvex.mm"
include "elsuc.mm"
include "sylib.mm"
include "orcomd.mm"
include "cdom.mm"
include "csdm.mm"
include "wn.mm"
include "cvv.mm"
include "elpwi.mm"
include "ad2antlr.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "ccf.mm"
include "rankcf.mm"
include "fveq2.mm"
include "c0.mm"
include "wne.mm"
include "elina.mm"
include "simp2bi.mm"
include "sylan9eqr.mm"
include "breq2d.mm"
include "mtbii.mm"
include "inar1.mm"
include "sdomentr.mm"
include "expcom.mm"
include "adantr.mm"
include "mtod.mm"
include "adantlr.mm"
include "bren2.mm"
include "sylanbrc.mm"
include "ex.mm"
include "cima.mm"
include "cdm.mm"
include "r1elwf.mm"
include "wfn.mm"
include "r1fnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "syl6eleqr.mm"
include "rankr1ag.mm"
include "biimprd.mm"
include "orim12d.mm"
include "mpd.mm"
include "eltsk2g.mm"

theorem inatsk
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. Inacc -> ( R1 ` A ) e. Tarski )

  proof
    cA
    cina
    wcel
    #
    vx
    cv
    #
    cpw
    #
    cA
    cr1
    cfv
    #
    wss
    #
    @2
    @3
    wcel
    #
    wa
    #
    vx
    @3
    wral
    #
    @1
    @3
    cen
    wbr
    #
    @1
    @3
    wcel
    #
    wo
    #
    vx
    @3
    cpw
    #
    wral
    #
    @3
    ctsk
    wcel
    #
    @0
    @6
    vx
    @3
    @0
    @9
    wa
    @5
    @4
    @0
    @9
    @5
    @0
    cA
    cwina
    wcel
    #
    @9
    @5
    wi
    cA
    inawina
    #
    @14
    @9
    @1
    vy
    cv
    #
    cr1
    cfv
    #
    wcel
    #
    vy
    cA
    wrex
    #
    @5
    @14
    @9
    @1
    vy
    cA
    @17
    ciun
    #
    wcel
    @19
    @14
    @3
    @20
    @1
    @14
    cA
    con0
    wcel
    #
    cA
    wlim
    #
    @3
    @20
    wceq
    cA
    winaon
    #
    cA
    winalim
    #
    vy
    cA
    con0
    r1lim
    syl2anc
    eleq2d
    vy
    @1
    cA
    @17
    eliun
    syl6bb
    @14
    @18
    @5
    vy
    cA
    @14
    @16
    cA
    wcel
    #
    wa
    #
    @18
    @2
    @16
    csuc
    #
    cr1
    cfv
    #
    wcel
    #
    @5
    @26
    @16
    con0
    wcel
    #
    @18
    @29
    wb
    @14
    @21
    @25
    @30
    @23
    cA
    @16
    onelon
    sylan
    @1
    @16
    r1pw
    syl
    @26
    @28
    @3
    @2
    @14
    @25
    @28
    @3
    wss
    #
    @14
    @25
    @27
    cA
    wcel
    #
    @31
    @14
    @22
    @25
    @32
    wb
    @24
    cA
    @16
    limsuc
    syl
    @14
    @21
    @32
    @31
    wi
    @23
    @27
    cA
    r1ord2
    syl
    sylbid
    imp
    sseld
    sylbid
    rexlimdva
    sylbid
    syl
    imp
    @5
    @2
    @3
    cuni
    @3
    @2
    @3
    elssuni
    cA
    r1tr2
    syl6ss
    jccil
    ralrimiva
    @0
    @10
    vx
    @11
    @0
    @1
    @11
    wcel
    #
    wa
    #
    @1
    crnk
    cfv
    #
    cA
    wceq
    #
    @35
    cA
    wcel
    #
    wo
    @10
    @34
    @37
    @36
    @34
    @35
    cA
    csuc
    #
    wcel
    #
    @37
    @36
    wo
    @0
    @33
    @39
    @0
    @33
    @1
    @38
    cr1
    cfv
    #
    wcel
    #
    @39
    @0
    @21
    @41
    @33
    wb
    @0
    @14
    @21
    @15
    @23
    syl
    #
    @21
    @40
    @11
    @1
    cA
    r1suc
    eleq2d
    syl
    #
    @1
    @38
    rankr1ai
    syl6bir
    imp
    @35
    cA
    @1
    crnk
    fvex
    elsuc
    sylib
    orcomd
    @34
    @36
    @8
    @37
    @9
    @34
    @36
    @8
    @34
    @36
    wa
    #
    @1
    @3
    cdom
    wbr
    #
    @1
    @3
    csdm
    wbr
    #
    wn
    #
    @8
    @3
    cvv
    wcel
    #
    @44
    @1
    @3
    wss
    #
    @45
    cA
    cr1
    fvex
    #
    @33
    @49
    @0
    @36
    @1
    @3
    elpwi
    ad2antlr
    @1
    @3
    cvv
    ssdomg
    mpsyl
    @0
    @36
    @47
    @33
    @0
    @36
    wa
    #
    @46
    @1
    cA
    csdm
    wbr
    #
    @51
    @1
    @35
    ccf
    cfv
    #
    csdm
    wbr
    @52
    @1
    rankcf
    @51
    @53
    cA
    @1
    csdm
    @36
    @0
    @53
    cA
    ccf
    cfv
    #
    cA
    @35
    cA
    ccf
    fveq2
    @0
    cA
    c0
    wne
    @54
    cA
    wceq
    @2
    cA
    csdm
    wbr
    vx
    cA
    wral
    vx
    cA
    elina
    simp2bi
    sylan9eqr
    breq2d
    mtbii
    @0
    @46
    @52
    wi
    #
    @36
    @0
    @3
    cA
    cen
    wbr
    #
    @55
    cA
    inar1
    @46
    @56
    @52
    @1
    @3
    cA
    sdomentr
    expcom
    syl
    adantr
    mtod
    adantlr
    @1
    @3
    bren2
    sylanbrc
    ex
    @34
    @9
    @37
    @34
    @1
    cr1
    con0
    cima
    cuni
    wcel
    #
    cA
    cr1
    cdm
    #
    wcel
    #
    @9
    @37
    wb
    @0
    @33
    @57
    @0
    @33
    @41
    @57
    @43
    @1
    @38
    r1elwf
    syl6bir
    imp
    @0
    @59
    @33
    @0
    cA
    con0
    @58
    @42
    cr1
    con0
    wfn
    @58
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    syl6eleqr
    adantr
    @1
    cA
    rankr1ag
    syl2anc
    biimprd
    orim12d
    mpd
    ralrimiva
    @48
    @13
    @7
    @12
    wa
    wb
    @50
    vx
    @3
    cvv
    eltsk2g
    ax-mp
    sylanbrc
end
