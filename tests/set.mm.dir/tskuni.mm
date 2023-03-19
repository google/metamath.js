include "ctsk.mm"
include "wcel.mm"
include "wtr.mm"
include "w3a.mm"
include "cuni.mm"
include "cen.mm"
include "wbr.mm"
include "wn.mm"
include "ccrd.mm"
include "cfv.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wa.mm"
include "cima.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "wne.mm"
include "ccf.mm"
include "csdm.mm"
include "tsksdom.mm"
include "cardidg.mm"
include "ensymd.mm"
include "adantr.mm"
include "sdomentr.mm"
include "syl2anc.mm"
include "cdom.mm"
include "cmpt.mm"
include "crn.mm"
include "eqid.mm"
include "rnmpt.mm"
include "cdm.mm"
include "wfo.mm"
include "con0.mm"
include "cardon.mm"
include "sdomdom.mm"
include "ondomen.mm"
include "sylancr.mm"
include "adantl.mm"
include "wfn.mm"
include "vex.mm"
include "imaex.mm"
include "fnmpti.mm"
include "dffn4.mm"
include "mpbi.mm"
include "fodomnum.mm"
include "mpisyl.mm"
include "syl5eqbrr.mm"
include "domsdomtr.mm"
include "sylancom.mm"
include "adantll.mm"
include "mpdan.mm"
include "cina.mm"
include "c0.mm"
include "ne0i.mm"
include "tskcard.mm"
include "sylan2.mm"
include "cpw.mm"
include "wral.mm"
include "elina.mm"
include "simp2bi.mm"
include "syl.mm"
include "breqtrrd.mm"
include "3adant2.mm"
include "wlim.mm"
include "wss.mm"
include "wi.mm"
include "cwina.mm"
include "inawina.mm"
include "winalim.mm"
include "3syl.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "imassrn.mm"
include "f1ofo.mm"
include "forn.mm"
include "syl5sseq.mm"
include "ad2antlr.mm"
include "wf1.mm"
include "f1of1.mm"
include "elssuni.mm"
include "f1imaen.mm"
include "syl2an.mm"
include "simpl1.mm"
include "trss.mm"
include "imp.mm"
include "3adant1.mm"
include "sselda.mm"
include "adantlr.mm"
include "ensdomtr.mm"
include "sseq1.mm"
include "breq1.mm"
include "anbi12d.mm"
include "biimprcd.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "fvex.mm"
include "cfslb2n.mm"
include "mpd.mm"
include "ciun.mm"
include "dfiun2.mm"
include "ralrimivw.mm"
include "iunss.mm"
include "sylibr.mm"
include "wf.mm"
include "fof.mm"
include "foelrn.mm"
include "ex.mm"
include "eluni2.mm"
include "nfv.mm"
include "nfiu1.mm"
include "nfel2.mm"
include "ssiun2.mm"
include "3ad2ant2.mm"
include "ffn.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "3exp.mm"
include "rexlimd.mm"
include "eleq1a.mm"
include "syl6.mm"
include "rexlimdv.mm"
include "sylsyld.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "syl5eqr.mm"
include "necon3ai.mm"
include "pm2.01da.mm"
include "nexdv.mm"
include "entr.mm"
include "bren.mm"
include "sylib.mm"
include "expcom.mm"
include "mtod.mm"
include "wo.mm"
include "uniss.mm"
include "df-tr.mm"
include "biimpi.mm"
include "sylan9ss.mm"
include "syld.mm"
include "tsken.mm"
include "3impb.mm"
include "ord.mm"

theorem tskuni
  let cA: class A
  let cT: class T
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( T e. Tarski /\ Tr T /\ A e. T ) -> U. A e. T )

  proof
    cT
    ctsk
    wcel
    #
    cT
    wtr
    #
    cA
    cT
    wcel
    #
    w3a
    #
    cA
    cuni
    #
    cT
    cen
    wbr
    #
    wn
    @4
    cT
    wcel
    #
    @3
    @5
    @4
    cT
    ccrd
    cfv
    #
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    @3
    @9
    vf
    @3
    @9
    @3
    @9
    wa
    #
    vz
    cv
    #
    @8
    vx
    cv
    #
    cima
    #
    wceq
    #
    vx
    cA
    wrex
    #
    vz
    cab
    #
    cuni
    #
    @7
    wne
    #
    @9
    wn
    @11
    @17
    @7
    ccf
    cfv
    #
    csdm
    wbr
    #
    @19
    @3
    @21
    @9
    @0
    @2
    @21
    @1
    @0
    @2
    wa
    #
    @17
    @7
    @20
    csdm
    @22
    cA
    @7
    csdm
    wbr
    #
    @17
    @7
    csdm
    wbr
    #
    @22
    cA
    cT
    csdm
    wbr
    cT
    @7
    cen
    wbr
    #
    @23
    cA
    cT
    tsksdom
    @0
    @25
    @2
    @0
    @7
    cT
    cT
    ctsk
    cardidg
    ensymd
    #
    adantr
    cA
    cT
    @7
    sdomentr
    syl2anc
    @2
    @23
    @24
    @0
    @2
    @23
    @17
    cA
    cdom
    wbr
    @24
    @2
    @23
    wa
    #
    @17
    vx
    cA
    @14
    cmpt
    #
    crn
    #
    cA
    cdom
    vx
    vz
    cA
    @14
    @28
    @28
    eqid
    #
    rnmpt
    @27
    cA
    ccrd
    cdm
    wcel
    #
    cA
    @29
    @28
    wfo
    #
    @29
    cA
    cdom
    wbr
    @23
    @31
    @2
    @23
    @7
    con0
    wcel
    cA
    @7
    cdom
    wbr
    @31
    cT
    cardon
    cA
    @7
    sdomdom
    @7
    cA
    ondomen
    sylancr
    adantl
    @28
    cA
    wfn
    @32
    vx
    cA
    @14
    @28
    @8
    @13
    vf
    vex
    imaex
    #
    @30
    fnmpti
    cA
    @28
    dffn4
    mpbi
    cA
    @29
    @28
    fodomnum
    mpisyl
    syl5eqbrr
    @17
    cA
    @7
    domsdomtr
    sylancom
    adantll
    mpdan
    @22
    @7
    cina
    wcel
    #
    @20
    @7
    wceq
    #
    @2
    @0
    cT
    c0
    wne
    @34
    cT
    cA
    ne0i
    cT
    tskcard
    sylan2
    #
    @34
    @7
    c0
    wne
    @35
    @13
    cpw
    @7
    csdm
    wbr
    vx
    @7
    wral
    vx
    @7
    elina
    simp2bi
    #
    syl
    breqtrrd
    3adant2
    adantr
    @11
    @7
    wlim
    #
    vy
    cv
    #
    @7
    wss
    #
    @39
    @20
    csdm
    wbr
    #
    wa
    #
    vy
    @17
    wral
    @21
    @19
    wi
    @11
    @34
    @7
    cwina
    wcel
    @38
    @3
    @34
    @9
    @0
    @2
    @34
    @1
    @36
    3adant2
    adantr
    #
    @7
    inawina
    @7
    winalim
    3syl
    @11
    @42
    vy
    @17
    @39
    @17
    wcel
    @39
    @14
    wceq
    #
    vx
    cA
    wrex
    #
    @11
    @42
    @16
    @45
    vz
    @39
    vy
    vex
    @12
    @39
    wceq
    @15
    @44
    vx
    cA
    @12
    @39
    @14
    eqeq1
    rexbidv
    elab
    @11
    @44
    @42
    vx
    cA
    @11
    @13
    cA
    wcel
    #
    wa
    #
    @14
    @7
    wss
    #
    @14
    @20
    csdm
    wbr
    #
    @44
    @42
    wi
    @9
    @48
    @3
    @46
    @9
    @8
    crn
    #
    @14
    @7
    @8
    @13
    imassrn
    @9
    @4
    @7
    @8
    wfo
    #
    @50
    @7
    wceq
    @4
    @7
    @8
    f1ofo
    #
    @4
    @7
    @8
    forn
    syl
    syl5sseq
    #
    ad2antlr
    @47
    @14
    @7
    @20
    csdm
    @47
    @14
    @13
    cen
    wbr
    #
    @13
    @7
    csdm
    wbr
    #
    @14
    @7
    csdm
    wbr
    @9
    @46
    @54
    @3
    @9
    @4
    @7
    @8
    wf1
    @13
    @4
    wss
    #
    @54
    @46
    @4
    @7
    @8
    f1of1
    @13
    cA
    elssuni
    #
    @4
    @7
    @13
    @8
    vx
    vex
    f1imaen
    syl2an
    adantll
    @3
    @46
    @55
    @9
    @3
    @46
    wa
    #
    @13
    cT
    csdm
    wbr
    #
    @25
    @55
    @58
    @0
    @13
    cT
    wcel
    @59
    @0
    @1
    @2
    @46
    simpl1
    #
    @3
    cA
    cT
    @13
    @1
    @2
    cA
    cT
    wss
    #
    @0
    @1
    @2
    @61
    cT
    cA
    trss
    #
    imp
    3adant1
    sselda
    @13
    cT
    tsksdom
    syl2anc
    @58
    @0
    @25
    @60
    @26
    syl
    @13
    cT
    @7
    sdomentr
    syl2anc
    adantlr
    @14
    @13
    @7
    ensdomtr
    syl2anc
    @11
    @35
    @46
    @11
    @34
    @35
    @43
    @37
    syl
    adantr
    breqtrrd
    @44
    @42
    @48
    @49
    wa
    @44
    @40
    @48
    @41
    @49
    @39
    @14
    @7
    sseq1
    @39
    @14
    @20
    csdm
    breq1
    anbi12d
    biimprcd
    syl2anc
    rexlimdva
    syl5bi
    ralrimiv
    vy
    @7
    @17
    cT
    ccrd
    fvex
    cfslb2n
    syl2anc
    mpd
    @9
    @18
    @7
    @9
    @18
    vx
    cA
    @14
    ciun
    #
    @7
    vx
    vz
    cA
    @14
    @33
    dfiun2
    @9
    @63
    @7
    @9
    @48
    vx
    cA
    wral
    @63
    @7
    wss
    @9
    @48
    vx
    cA
    @53
    ralrimivw
    vx
    cA
    @14
    @7
    iunss
    sylibr
    @9
    vy
    @7
    @63
    @9
    @51
    @39
    @7
    wcel
    #
    @39
    @63
    wcel
    #
    wi
    @52
    @51
    @4
    @7
    @8
    wf
    #
    @64
    @39
    @12
    @8
    cfv
    #
    wceq
    #
    vz
    @4
    wrex
    #
    @65
    @4
    @7
    @8
    fof
    @51
    @64
    @69
    vz
    @4
    @7
    @39
    @8
    foelrn
    ex
    @66
    @68
    @65
    vz
    @4
    @66
    @12
    @4
    wcel
    #
    @67
    @63
    wcel
    #
    @68
    @65
    wi
    @70
    @12
    @13
    wcel
    #
    vx
    cA
    wrex
    @66
    @71
    vx
    @12
    cA
    eluni2
    @66
    @72
    @71
    vx
    cA
    @66
    vx
    nfv
    vx
    @67
    @63
    vx
    cA
    @14
    nfiu1
    nfel2
    @66
    @46
    @72
    @71
    @66
    @46
    @72
    w3a
    #
    @14
    @63
    @67
    @46
    @66
    @14
    @63
    wss
    @72
    vx
    cA
    @14
    ssiun2
    3ad2ant2
    @73
    @8
    @4
    wfn
    #
    @56
    @72
    @67
    @14
    wcel
    @66
    @46
    @74
    @72
    @4
    @7
    @8
    ffn
    3ad2ant1
    @46
    @66
    @56
    @72
    @57
    3ad2ant2
    @66
    @46
    @72
    simp3
    @4
    @13
    @8
    @12
    fnfvima
    syl3anc
    sseldd
    3exp
    rexlimd
    syl5bi
    @67
    @63
    @39
    eleq1a
    syl6
    rexlimdv
    sylsyld
    syl
    ssrdv
    eqssd
    syl5eqr
    necon3ai
    syl
    pm2.01da
    nexdv
    @0
    @1
    @5
    @10
    wi
    @2
    @5
    @0
    @10
    @5
    @0
    wa
    @4
    @7
    cen
    wbr
    #
    @10
    @0
    @5
    @25
    @75
    @26
    @4
    cT
    @7
    entr
    sylan2
    @4
    @7
    vf
    bren
    sylib
    expcom
    3ad2ant1
    mtod
    @3
    @5
    @6
    @0
    @1
    @2
    @5
    @6
    wo
    #
    @1
    @2
    wa
    @0
    @4
    cT
    wss
    #
    @76
    @1
    @2
    @77
    @1
    @2
    @61
    @77
    @62
    @61
    @1
    @77
    @61
    @1
    @4
    cT
    cuni
    #
    cT
    cA
    cT
    uniss
    @1
    @78
    cT
    wss
    cT
    df-tr
    biimpi
    sylan9ss
    expcom
    syld
    imp
    @4
    cT
    tsken
    sylan2
    3impb
    ord
    mpd
end
