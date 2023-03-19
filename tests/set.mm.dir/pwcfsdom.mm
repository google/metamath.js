include "con0.mm"
include "wcel.mm"
include "cale.mm"
include "cfv.mm"
include "ccf.mm"
include "cmap.mm"
include "co.mm"
include "csdm.mm"
include "wbr.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "csuc.mm"
include "wrex.mm"
include "cvv.mm"
include "wlim.mm"
include "wa.mm"
include "w3o.mm"
include "onzsl.mm"
include "biimpi.mm"
include "com.mm"
include "cfom.mm"
include "aleph0.mm"
include "fveq2i.mm"
include "3eqtr4i.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "c2o.mm"
include "cdom.mm"
include "cpw.mm"
include "cen.mm"
include "fvex.mm"
include "canth2.mm"
include "pw2en.mm"
include "sdomentr.mm"
include "mp2an.mm"
include "wss.mm"
include "alephon.mm"
include "alephgeom.mm"
include "omelon.mm"
include "2onn.mm"
include "onelss.mm"
include "mp2.mm"
include "sstr.mm"
include "mpan.mm"
include "sylbi.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "mapdom1.mm"
include "syl.mm"
include "sdomdomtr.mm"
include "sylancr.mm"
include "oveq2.mm"
include "breq2d.mm"
include "syl5ibrcom.mm"
include "syl5.mm"
include "alephreg.mm"
include "rexlimivw.mm"
include "wi.mm"
include "wf.mm"
include "wsmo.mm"
include "wral.mm"
include "w3a.mm"
include "wex.mm"
include "cfsmo.mm"
include "cixp.mm"
include "limelon.mm"
include "ciun.mm"
include "crn.mm"
include "cuni.mm"
include "cab.mm"
include "wfn.mm"
include "ffn.mm"
include "fnrnfv.mm"
include "unieqd.mm"
include "dfiun2.mm"
include "syl6eqr.mm"
include "ad2antrl.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "sseq2.mm"
include "rspcev.mm"
include "ex.mm"
include "rexlimdva.mm"
include "ralimdv.mm"
include "imp.mm"
include "adantl.mm"
include "wb.mm"
include "alephislim.mm"
include "frn.mm"
include "adantr.mm"
include "coflim.mm"
include "syl2an.mm"
include "mpbird.mm"
include "eqtr3d.mm"
include "char.mm"
include "ffvelrn.mm"
include "oneli.mm"
include "ccrd.mm"
include "harcard.mm"
include "iscard.mm"
include "simprbi.mm"
include "ax-mp.mm"
include "domrefg.mm"
include "elharval.mm"
include "biimpri.mm"
include "mpan2.mm"
include "breq1.mm"
include "rspccv.mm"
include "3syl.mm"
include "harcl.mm"
include "fvmptg.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "konigth.mm"
include "eqbrtrrd.mm"
include "ovex.mm"
include "alephlim.mm"
include "eleq2d.mm"
include "eliun.mm"
include "alephcard.mm"
include "eleq2i.mm"
include "cardsdomelir.mm"
include "sylbir.mm"
include "wn.mm"
include "domnsym.mm"
include "con2i.mm"
include "ontri1.mm"
include "sylibr.mm"
include "alephord2i.mm"
include "ontr2.mm"
include "syl2anr.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "sylan9r.mm"
include "cmpt.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "fmptd.mm"
include "ss2ixp.mm"
include "ixpconst.mm"
include "syl6sseq.mm"
include "adantrr.mm"
include "syl2anc.mm"
include "expcom.mm"
include "3adant2.mm"
include "exlimiv.mm"
include "mp2b.mm"
include "a1i.mm"
include "3jaod.mm"
include "mpd.mm"
include "cdm.mm"
include "alephfnon.mm"
include "fndm.mm"
include "ndmfv.mm"
include "c1o.mm"
include "wne.mm"
include "1n0.mm"
include "1on.mm"
include "elexi.mm"
include "0sdom.mm"
include "mpbir.mm"
include "id.mm"
include "cf0.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "0ex.mm"
include "map0e.mm"
include "breq12d.mm"
include "mpbiri.mm"
include "sylnbir.mm"
include "pm2.61i.mm"

theorem pwcfsdom
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let cH: class H
  let vw: setvar w
  let vz: setvar z
  let vx: setvar x
  assume pwcfsdom.1: |- H = ( y e. ( cf ` ( aleph ` A ) ) |-> ( har ` ( f ` y ) ) )

  disjoint A f
  disjoint A y
  disjoint f y
  disjoint A w
  disjoint A z
  disjoint f w
  disjoint f z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint A x
  disjoint f x
  disjoint x y
  disjoint H x
  assert |- ( aleph ` A ) ~< ( ( aleph ` A ) ^m ( cf ` ( aleph ` A ) ) )

  proof
    cA
    con0
    wcel
    #
    cA
    cale
    cfv
    #
    @1
    @1
    ccf
    cfv
    #
    cmap
    co
    #
    csdm
    wbr
    #
    @0
    cA
    c0
    wceq
    #
    cA
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
    cA
    cvv
    wcel
    cA
    wlim
    wa
    #
    w3o
    #
    @4
    @0
    @11
    vx
    cA
    onzsl
    biimpi
    @0
    @5
    @4
    @9
    @10
    @5
    @2
    @1
    wceq
    #
    @0
    @4
    @5
    c0
    cale
    cfv
    #
    ccf
    cfv
    #
    @13
    @2
    @1
    com
    ccf
    cfv
    com
    @14
    @13
    cfom
    @13
    com
    ccf
    aleph0
    fveq2i
    aleph0
    3eqtr4i
    @5
    @1
    @13
    ccf
    cA
    c0
    cale
    fveq2
    #
    fveq2d
    @15
    3eqtr4a
    @0
    @4
    @12
    @1
    @1
    @1
    cmap
    co
    #
    csdm
    wbr
    #
    @0
    @1
    c2o
    @1
    cmap
    co
    #
    csdm
    wbr
    #
    @18
    @16
    cdom
    wbr
    #
    @17
    @1
    @1
    cpw
    #
    csdm
    wbr
    @21
    @18
    cen
    wbr
    @19
    @1
    cA
    cale
    fvex
    #
    canth2
    @1
    @22
    pw2en
    @1
    @21
    @18
    sdomentr
    mp2an
    @0
    c2o
    @1
    cdom
    wbr
    #
    @20
    @1
    con0
    wcel
    #
    @0
    c2o
    @1
    wss
    #
    @23
    cA
    alephon
    #
    @0
    com
    @1
    wss
    #
    @25
    cA
    alephgeom
    c2o
    com
    wss
    #
    @27
    @25
    com
    con0
    wcel
    c2o
    com
    wcel
    @28
    omelon
    2onn
    com
    c2o
    onelss
    mp2
    c2o
    com
    @1
    sstr
    mpan
    sylbi
    c2o
    @1
    con0
    ssdomg
    mpsyl
    c2o
    @1
    @1
    mapdom1
    syl
    @1
    @18
    @16
    sdomdomtr
    sylancr
    @12
    @3
    @16
    @1
    csdm
    @2
    @1
    @1
    cmap
    oveq2
    breq2d
    syl5ibrcom
    #
    syl5
    @9
    @12
    @0
    @4
    @8
    @12
    vx
    con0
    @8
    @7
    cale
    cfv
    #
    ccf
    cfv
    @30
    @2
    @1
    @6
    alephreg
    @8
    @1
    @30
    ccf
    cA
    @7
    cale
    fveq2
    #
    fveq2d
    @31
    3eqtr4a
    rexlimivw
    @29
    syl5
    @10
    @4
    wi
    #
    @0
    @24
    @2
    @1
    vf
    cv
    #
    wf
    #
    @33
    wsmo
    #
    vz
    cv
    #
    vw
    cv
    #
    @33
    cfv
    #
    wss
    #
    vw
    @2
    wrex
    #
    vz
    @1
    wral
    #
    w3a
    #
    vf
    wex
    @32
    @26
    vz
    vw
    @1
    vf
    cfsmo
    @42
    @32
    vf
    @34
    @41
    @32
    @35
    @10
    @34
    @41
    wa
    #
    @4
    @10
    @43
    wa
    @1
    vx
    @2
    @6
    cH
    cfv
    #
    cixp
    #
    csdm
    wbr
    #
    @45
    @3
    cdom
    wbr
    #
    @4
    @10
    @0
    @43
    @46
    cA
    cvv
    limelon
    #
    @0
    @43
    wa
    #
    vx
    @2
    @6
    @33
    cfv
    #
    ciun
    #
    @1
    @45
    csdm
    @49
    @33
    crn
    #
    cuni
    #
    @51
    @1
    @34
    @53
    @51
    wceq
    @0
    @41
    @34
    @53
    vy
    cv
    #
    @50
    wceq
    vx
    @2
    wrex
    vy
    cab
    #
    cuni
    #
    @51
    @34
    @33
    @2
    wfn
    #
    @53
    @56
    wceq
    @2
    @1
    @33
    ffn
    #
    @57
    @52
    @55
    vx
    vy
    @2
    @33
    fnrnfv
    unieqd
    syl
    vx
    vy
    @2
    @50
    @6
    @33
    fvex
    #
    dfiun2
    syl6eqr
    ad2antrl
    @49
    @53
    @1
    wceq
    #
    @36
    @54
    wss
    #
    vy
    @52
    wrex
    #
    vz
    @1
    wral
    #
    @43
    @63
    @0
    @34
    @41
    @63
    @34
    @40
    @62
    vz
    @1
    @34
    @39
    @62
    vw
    @2
    @34
    @37
    @2
    wcel
    #
    wa
    #
    @39
    @62
    @65
    @38
    @52
    wcel
    #
    @39
    @62
    @34
    @57
    @64
    @66
    @58
    @2
    @37
    @33
    fnfvelrn
    sylan
    @61
    @39
    vy
    @38
    @52
    @54
    @38
    @36
    sseq2
    rspcev
    sylan
    ex
    rexlimdva
    ralimdv
    imp
    adantl
    @0
    @1
    wlim
    #
    @52
    @1
    wss
    #
    @60
    @63
    wb
    @43
    @0
    @67
    cA
    alephislim
    biimpi
    @34
    @68
    @41
    @2
    @1
    @33
    frn
    adantr
    vz
    vy
    @1
    @52
    coflim
    syl2an
    mpbird
    eqtr3d
    @34
    @51
    @45
    csdm
    wbr
    #
    @0
    @41
    @34
    @50
    @44
    csdm
    wbr
    #
    vx
    @2
    wral
    @69
    @34
    @70
    vx
    @2
    @34
    @6
    @2
    wcel
    #
    wa
    #
    @70
    @50
    @50
    char
    cfv
    #
    csdm
    wbr
    #
    @72
    @50
    @1
    wcel
    #
    @50
    con0
    wcel
    #
    @74
    @2
    @1
    @6
    @33
    ffvelrn
    #
    @1
    @50
    @26
    oneli
    @54
    @73
    csdm
    wbr
    #
    vy
    @73
    wral
    #
    @76
    @50
    @73
    wcel
    #
    @74
    @73
    ccrd
    cfv
    @73
    wceq
    #
    @79
    @50
    harcard
    @81
    @73
    con0
    wcel
    #
    @79
    vy
    @73
    iscard
    simprbi
    ax-mp
    @76
    @50
    @50
    cdom
    wbr
    #
    @80
    @50
    cvv
    wcel
    @83
    @59
    @50
    cvv
    domrefg
    ax-mp
    @80
    @76
    @83
    wa
    @50
    @50
    elharval
    biimpri
    mpan2
    @78
    @74
    vy
    @50
    @73
    @54
    @50
    @73
    csdm
    breq1
    rspccv
    mpsyl
    3syl
    @71
    @70
    @74
    wb
    @34
    @71
    @44
    @73
    @50
    csdm
    @71
    @82
    @44
    @73
    wceq
    @50
    harcl
    #
    vy
    @6
    @54
    @33
    cfv
    #
    char
    cfv
    #
    @73
    @2
    con0
    cH
    @54
    @6
    wceq
    @85
    @50
    char
    @54
    @6
    @33
    fveq2
    fveq2d
    #
    pwcfsdom.1
    fvmptg
    mpan2
    breq2d
    adantl
    mpbird
    ralrimiva
    @2
    @45
    @51
    vx
    @33
    cH
    @1
    ccf
    fvex
    #
    @51
    eqid
    @45
    eqid
    konigth
    syl
    ad2antrl
    eqbrtrrd
    sylan
    @10
    @34
    @47
    @41
    @3
    cvv
    wcel
    @10
    @34
    wa
    #
    @45
    @3
    wss
    #
    @47
    @1
    @2
    cmap
    ovex
    @89
    @2
    @1
    cH
    wf
    #
    @44
    @1
    wss
    #
    vx
    @2
    wral
    #
    @90
    @89
    vx
    @2
    @73
    @1
    cH
    @89
    @71
    @73
    @1
    wcel
    #
    @34
    @71
    @75
    @10
    @94
    @34
    @71
    @75
    @77
    ex
    @10
    @75
    @50
    vy
    cA
    @54
    cale
    cfv
    #
    ciun
    #
    wcel
    #
    @94
    @10
    @1
    @96
    @50
    vy
    cA
    cvv
    alephlim
    eleq2d
    @10
    @0
    @97
    @94
    wi
    @48
    @97
    @50
    @95
    wcel
    #
    vy
    cA
    wrex
    @0
    @94
    vy
    @50
    cA
    @95
    eliun
    @0
    @98
    @94
    vy
    cA
    @0
    @54
    cA
    wcel
    #
    @98
    @94
    @98
    @73
    @95
    wss
    #
    @95
    @1
    wcel
    #
    @94
    @0
    @99
    wa
    @98
    @50
    @95
    csdm
    wbr
    #
    @100
    @98
    @50
    @95
    ccrd
    cfv
    #
    wcel
    @102
    @103
    @95
    @50
    @54
    alephcard
    eleq2i
    @50
    @95
    cardsdomelir
    sylbir
    @102
    @95
    @73
    wcel
    #
    wn
    #
    @100
    @104
    @102
    @104
    @95
    @50
    cdom
    wbr
    #
    @102
    wn
    @104
    @95
    con0
    wcel
    #
    @106
    @50
    @95
    elharval
    simprbi
    @95
    @50
    domnsym
    syl
    con2i
    @82
    @107
    @100
    @105
    wb
    @84
    @54
    alephon
    @73
    @95
    ontri1
    mp2an
    sylibr
    syl
    @0
    @99
    @101
    @54
    cA
    alephord2i
    imp
    @82
    @24
    @100
    @101
    wa
    @94
    wi
    @84
    @26
    @73
    @95
    @1
    ontr2
    mp2an
    syl2anr
    exp31
    rexlimdv
    syl5bi
    syl
    sylbid
    sylan9r
    imp
    cH
    vy
    @2
    @86
    cmpt
    vx
    @2
    @73
    cmpt
    pwcfsdom.1
    vy
    vx
    @2
    @86
    @73
    @87
    cbvmptv
    eqtri
    fmptd
    @91
    @92
    vx
    @2
    @24
    @91
    @71
    wa
    @44
    @1
    wcel
    @92
    @26
    @2
    @1
    @6
    cH
    ffvelrn
    @1
    @44
    onelss
    mpsyl
    ralrimiva
    @93
    @45
    vx
    @2
    @1
    cixp
    @3
    vx
    @2
    @44
    @1
    ss2ixp
    vx
    @2
    @1
    @88
    @22
    ixpconst
    syl6sseq
    3syl
    @45
    @3
    cvv
    ssdomg
    mpsyl
    adantrr
    @1
    @45
    @3
    sdomdomtr
    syl2anc
    expcom
    3adant2
    exlimiv
    mp2b
    a1i
    3jaod
    mpd
    @0
    cA
    cale
    cdm
    #
    wcel
    #
    @4
    @108
    con0
    cA
    cale
    con0
    wfn
    @108
    con0
    wceq
    alephfnon
    con0
    cale
    fndm
    ax-mp
    eleq2i
    @109
    wn
    @1
    c0
    wceq
    #
    @4
    cA
    cale
    ndmfv
    @110
    @4
    c0
    c1o
    csdm
    wbr
    #
    @111
    c1o
    c0
    wne
    1n0
    c1o
    c1o
    con0
    1on
    elexi
    0sdom
    mpbir
    @110
    @1
    c0
    @3
    c1o
    csdm
    @110
    id
    #
    @110
    @3
    c0
    c0
    cmap
    co
    #
    c1o
    @110
    @1
    c0
    @2
    c0
    cmap
    @112
    @110
    @2
    c0
    ccf
    cfv
    c0
    @1
    c0
    ccf
    fveq2
    cf0
    syl6eq
    oveq12d
    c0
    cvv
    wcel
    @113
    c1o
    wceq
    0ex
    c0
    cvv
    map0e
    ax-mp
    syl6eq
    breq12d
    mpbiri
    syl
    sylnbir
    pm2.61i
end
