include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cmap.mm"
include "co.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wss.mm"
include "cen.mm"
include "wa.mm"
include "cab.mm"
include "c0.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq2.mm"
include "anbi2d.mm"
include "abbidv.mm"
include "breq12d.mm"
include "wne.mm"
include "cxp.mm"
include "cvv.mm"
include "simpl2.mm"
include "reldom.mm"
include "brrelexi.mm"
include "syl.mm"
include "brrelex2i.mm"
include "xpcomeng.mm"
include "syl2anc.mm"
include "simpl3.mm"
include "simpr.mm"
include "mapdom3.mm"
include "syl3anc.mm"
include "numdom.mm"
include "simpl1.mm"
include "infxpabs.mm"
include "syl22anc.mm"
include "entr.mm"
include "ssenen.mm"
include "relen.mm"
include "abid2.mm"
include "wf.mm"
include "elmapi.mm"
include "fssxp.mm"
include "wfun.mm"
include "ffun.mm"
include "vex.mm"
include "fundmen.mm"
include "ensym.mm"
include "3syl.mm"
include "fdm.mm"
include "breqtrd.mm"
include "jca.mm"
include "ss2abi.mm"
include "eqsstr3i.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "domentr.mm"
include "crn.mm"
include "cmpt.mm"
include "ovex.mm"
include "mptex.mm"
include "rnex.mm"
include "wrex.mm"
include "wex.mm"
include "wf1o.mm"
include "ad2antll.mm"
include "bren.mm"
include "sylib.mm"
include "f1of.mm"
include "adantl.mm"
include "simplrl.mm"
include "fssd.mm"
include "wb.mm"
include "elmapd.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "eqcomd.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"
include "ss2abdv.mm"
include "eqid.mm"
include "rnmpt.mm"
include "syl6sseqr.mm"
include "mpsyl.mm"
include "wfn.mm"
include "wral.mm"
include "rgenw.mm"
include "fnmpt.mm"
include "mp1i.mm"
include "dffn4.mm"
include "fodomnum.mm"
include "sylc.mm"
include "domtr.mm"
include "sbth.mm"
include "c1o.mm"
include "3ad2ant1.mm"
include "map0e.mm"
include "1onn.mm"
include "elexi.mm"
include "enref.mm"
include "csn.mm"
include "df-sn.mm"
include "df1o2.mm"
include "en0.mm"
include "anbi2i.mm"
include "0ss.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "pm4.71ri.mm"
include "bitr4i.mm"
include "abbii.mm"
include "3eqtr4ri.mm"
include "breqtrri.mm"
include "syl6eqbr.mm"
include "pm2.61ne.mm"

theorem infmap2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f

  disjoint A x
  disjoint B x
  disjoint f x
  disjoint A f
  disjoint B f
  assert |- ( ( _om ~<_ A /\ B ~<_ A /\ ( A ^m B ) e. dom card ) -> ( A ^m B ) ~~ { x | ( x C_ A /\ x ~~ B ) } )

  proof
    com
    cA
    cdom
    wbr
    #
    cB
    cA
    cdom
    wbr
    #
    cA
    cB
    cmap
    co
    #
    ccrd
    cdm
    #
    wcel
    #
    w3a
    #
    @2
    vx
    cv
    #
    cA
    wss
    #
    @6
    cB
    cen
    wbr
    #
    wa
    #
    vx
    cab
    #
    cen
    wbr
    #
    cA
    c0
    cmap
    co
    #
    @7
    @6
    c0
    cen
    wbr
    #
    wa
    #
    vx
    cab
    #
    cen
    wbr
    cB
    c0
    cB
    c0
    wceq
    #
    @2
    @12
    @10
    @15
    cen
    cB
    c0
    cA
    cmap
    oveq2
    @16
    @9
    @14
    vx
    @16
    @8
    @13
    @7
    cB
    c0
    @6
    cen
    breq2
    anbi2d
    abbidv
    breq12d
    @5
    cB
    c0
    wne
    #
    wa
    #
    @2
    @10
    cdom
    wbr
    #
    @10
    @2
    cdom
    wbr
    #
    @11
    @18
    @2
    @6
    cB
    cA
    cxp
    #
    wss
    #
    @8
    wa
    #
    vx
    cab
    #
    cdom
    wbr
    #
    @24
    @10
    cen
    wbr
    #
    @19
    @18
    @24
    cvv
    wcel
    #
    @2
    @24
    wss
    @25
    @18
    @26
    @27
    @18
    @21
    cA
    cen
    wbr
    #
    @26
    @18
    @21
    cA
    cB
    cxp
    #
    cen
    wbr
    #
    @29
    cA
    cen
    wbr
    #
    @28
    @18
    cB
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    @30
    @18
    @1
    @32
    @0
    @1
    @4
    @17
    simpl2
    #
    cB
    cA
    cdom
    reldom
    brrelexi
    syl
    #
    @18
    @1
    @33
    @34
    cB
    cA
    cdom
    reldom
    brrelex2i
    syl
    #
    cB
    cA
    cvv
    cvv
    xpcomeng
    syl2anc
    @18
    cA
    @3
    wcel
    #
    @0
    @17
    @1
    @31
    @18
    @4
    cA
    @2
    cdom
    wbr
    #
    @37
    @0
    @1
    @4
    @17
    simpl3
    #
    @18
    @33
    @32
    @17
    @38
    @36
    @35
    @5
    @17
    simpr
    #
    cA
    cB
    cvv
    cvv
    mapdom3
    syl3anc
    @2
    cA
    numdom
    syl2anc
    @0
    @1
    @4
    @17
    simpl1
    @40
    @34
    cA
    cB
    infxpabs
    syl22anc
    @21
    @29
    cA
    entr
    syl2anc
    vx
    @21
    cA
    cB
    ssenen
    syl
    #
    @24
    @10
    cen
    relen
    brrelexi
    syl
    @2
    @6
    @2
    wcel
    #
    vx
    cab
    @24
    vx
    @2
    abid2
    @42
    @23
    vx
    @42
    cB
    cA
    @6
    wf
    #
    @23
    @6
    cA
    cB
    elmapi
    @43
    @22
    @8
    cB
    cA
    @6
    fssxp
    @43
    @6
    @6
    cdm
    #
    cB
    cen
    @43
    @6
    wfun
    @44
    @6
    cen
    wbr
    @6
    @44
    cen
    wbr
    cB
    cA
    @6
    ffun
    @6
    vx
    vex
    fundmen
    @44
    @6
    ensym
    3syl
    cB
    cA
    @6
    fdm
    breqtrd
    jca
    syl
    ss2abi
    eqsstr3i
    @2
    @24
    cvv
    ssdomg
    mpisyl
    @41
    @2
    @24
    @10
    domentr
    syl2anc
    @18
    @10
    vf
    @2
    vf
    cv
    #
    crn
    #
    cmpt
    #
    crn
    #
    cdom
    wbr
    #
    @48
    @2
    cdom
    wbr
    #
    @20
    @48
    cvv
    wcel
    @18
    @10
    @48
    wss
    @49
    @47
    vf
    @2
    @46
    cA
    cB
    cmap
    ovex
    mptex
    rnex
    @18
    @10
    @6
    @46
    wceq
    #
    vf
    @2
    wrex
    #
    vx
    cab
    @48
    @18
    @9
    @52
    vx
    @18
    @9
    @52
    @18
    @9
    wa
    #
    @45
    @2
    wcel
    #
    @51
    wa
    #
    vf
    wex
    #
    @52
    @53
    cB
    @6
    @45
    wf1o
    #
    vf
    wex
    #
    @56
    @53
    cB
    @6
    cen
    wbr
    #
    @58
    @8
    @59
    @18
    @7
    @6
    cB
    ensym
    ad2antll
    cB
    @6
    vf
    bren
    sylib
    @53
    @57
    @55
    vf
    @53
    @57
    @55
    @53
    @57
    wa
    #
    @54
    @51
    @60
    @54
    cB
    cA
    @45
    wf
    #
    @60
    cB
    @6
    cA
    @45
    @57
    cB
    @6
    @45
    wf
    @53
    cB
    @6
    @45
    f1of
    adantl
    @18
    @7
    @8
    @57
    simplrl
    fssd
    @18
    @54
    @61
    wb
    @9
    @57
    @18
    cA
    cB
    @45
    cvv
    cvv
    @36
    @35
    elmapd
    ad2antrr
    mpbird
    @60
    @46
    @6
    @57
    @46
    @6
    wceq
    #
    @53
    @57
    cB
    @6
    @45
    wfo
    @62
    cB
    @6
    @45
    f1ofo
    cB
    @6
    @45
    forn
    syl
    adantl
    eqcomd
    jca
    ex
    eximdv
    mpd
    @51
    vf
    @2
    df-rex
    sylibr
    ex
    ss2abdv
    vf
    vx
    @2
    @46
    @47
    @47
    eqid
    #
    rnmpt
    syl6sseqr
    @10
    @48
    cvv
    ssdomg
    mpsyl
    @18
    @4
    @2
    @48
    @47
    wfo
    #
    @50
    @39
    @18
    @47
    @2
    wfn
    #
    @64
    @46
    cvv
    wcel
    #
    vf
    @2
    wral
    @65
    @18
    @66
    vf
    @2
    @45
    vf
    vex
    rnex
    rgenw
    vf
    @2
    @46
    @47
    cvv
    @63
    fnmpt
    mp1i
    @2
    @47
    dffn4
    sylib
    @2
    @48
    @47
    fodomnum
    sylc
    @10
    @48
    @2
    domtr
    syl2anc
    @2
    @10
    sbth
    syl2anc
    @5
    @12
    c1o
    @15
    cen
    @5
    @33
    @12
    c1o
    wceq
    @0
    @1
    @33
    @4
    com
    cA
    cdom
    reldom
    brrelex2i
    3ad2ant1
    cA
    cvv
    map0e
    syl
    c1o
    c1o
    @15
    cen
    c1o
    c1o
    com
    1onn
    elexi
    enref
    c0
    csn
    @6
    c0
    wceq
    #
    vx
    cab
    c1o
    @15
    vx
    c0
    df-sn
    df1o2
    @14
    @67
    vx
    @14
    @7
    @67
    wa
    @67
    @13
    @67
    @7
    @6
    en0
    anbi2i
    @67
    @7
    @67
    @7
    c0
    cA
    wss
    cA
    0ss
    @6
    c0
    cA
    sseq1
    mpbiri
    pm4.71ri
    bitr4i
    abbii
    3eqtr4ri
    breqtrri
    syl6eqbr
    pm2.61ne
end
