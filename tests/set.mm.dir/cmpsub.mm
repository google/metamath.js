include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "cuni.mm"
include "cv.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "eqid.mm"
include "iscmp.mm"
include "wb.mm"
include "cvv.mm"
include "id.mm"
include "topopn.mm"
include "ssexg.mm"
include "syl2anr.mm"
include "resttop.mm"
include "syldan.mm"
include "ibar.mm"
include "bicomd.mm"
include "syl.mm"
include "syl5bb.mm"
include "cab.mm"
include "vex.mm"
include "weq.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "wel.mm"
include "selpw.mm"
include "ssel2.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ex.mm"
include "sylbi.mm"
include "adantl.mm"
include "rexlimdv.mm"
include "simpll.mm"
include "sseq2i.mm"
include "uniexg.mm"
include "sylan2.mm"
include "ancoms.mm"
include "sylan2b.mm"
include "adantr.mm"
include "elrest.mm"
include "syl2anc.mm"
include "sylibrd.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "abrexex.mm"
include "elpw.mm"
include "sylibr.mm"
include "unieq.mm"
include "pweq.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "sylan.mm"
include "restuni.mm"
include "ad2antrr.mm"
include "ciun.mm"
include "inex1.mm"
include "dfiun2.mm"
include "incom.mm"
include "a1i.mm"
include "iuneq2dv.mm"
include "syl5eqr.mm"
include "iunin2.mm"
include "uniiun.mm"
include "eqcomi.mm"
include "ineq2d.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "eqtr2d.mm"
include "eqeq12d.mm"
include "eqeq1d.mm"
include "a1bi.mm"
include "elin.mm"
include "dfss3.mm"
include "ralbii.mm"
include "3bitri.mm"
include "anbi1i.mm"
include "bitri.mm"
include "wf.mm"
include "cfv.mm"
include "wex.mm"
include "ac6sfi.mm"
include "crn.mm"
include "frn.mm"
include "ad2antrl.mm"
include "rnex.mm"
include "cdom.mm"
include "wbr.mm"
include "simprr.mm"
include "wfo.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "fodomfi.mm"
include "adantll.mm"
include "ad2ant2r.mm"
include "domfi.mm"
include "elind.mm"
include "fveq2.mm"
include "rspccv.mm"
include "pm2.27.mm"
include "w3a.mm"
include "inss1.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "ssel.mm"
include "a1dd.mm"
include "3imp.mm"
include "fnfvelrn.mm"
include "expcom.mm"
include "3ad2ant1.mm"
include "syl5.mm"
include "jcad.mm"
include "3exp.mm"
include "syld.mm"
include "com3r.mm"
include "imp.mm"
include "com3l.mm"
include "impcom.mm"
include "fvex.mm"
include "eleq2.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl6.mm"
include "exlimdv.mm"
include "eluni.mm"
include "3imtr4g.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "jca.mm"
include "eximdv.mm"
include "com23.mm"
include "sseq2d.mm"
include "exlimiv.mm"
include "syl8.mm"
include "mpd.mm"
include "rexlimdva.mm"
include "syl5bir.mm"
include "sylbird.mm"
include "ralrimdva.mm"
include "cmpsublem.mm"
include "impbid.mm"
include "bitrd.mm"

theorem cmpsub
  let cS: class S
  let cJ: class J
  let cX: class X
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume cmpsub.1: |- X = U. J

  disjoint c d
  disjoint J c
  disjoint J d
  disjoint S c
  disjoint S d
  disjoint X c
  disjoint X d
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint c f
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint d f
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint J f
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s y
  disjoint s z
  disjoint J s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint J t
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint c x
  disjoint d x
  disjoint f x
  disjoint S f
  disjoint s x
  disjoint S s
  disjoint t x
  disjoint S t
  disjoint u x
  disjoint S u
  disjoint v x
  disjoint S v
  disjoint w x
  disjoint S w
  disjoint x z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X f
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( J |`t S ) e. Comp <-> A. c e. ~P J ( S C_ U. c -> E. d e. ( ~P c i^i Fin ) S C_ U. d ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cJ
    cS
    crest
    co
    #
    ccmp
    wcel
    #
    @3
    cuni
    #
    vs
    cv
    #
    cuni
    #
    wceq
    #
    @5
    vt
    cv
    #
    cuni
    #
    wceq
    #
    vt
    @6
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vs
    @3
    cpw
    #
    wral
    #
    cS
    vc
    cv
    #
    cuni
    #
    wss
    #
    cS
    vd
    cv
    #
    cuni
    #
    wss
    #
    vd
    @18
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vc
    cJ
    cpw
    #
    wral
    #
    @4
    @3
    ctop
    wcel
    #
    @17
    wa
    #
    @2
    @17
    vs
    vt
    @3
    @5
    @5
    eqid
    iscmp
    @2
    @30
    @31
    @17
    wb
    @0
    @1
    cS
    cvv
    wcel
    #
    @30
    @1
    @1
    cX
    cJ
    wcel
    @32
    @0
    @1
    id
    cJ
    cX
    cmpsub.1
    topopn
    cS
    cX
    cJ
    ssexg
    syl2anr
    cS
    cJ
    cvv
    resttop
    syldan
    @30
    @17
    @31
    @30
    @17
    ibar
    bicomd
    syl
    syl5bb
    @2
    @17
    @29
    @2
    @17
    @27
    vc
    @28
    @2
    @18
    @28
    wcel
    #
    wa
    #
    @17
    @5
    vx
    cv
    #
    vy
    cv
    #
    cS
    cin
    #
    wceq
    #
    vy
    @18
    wrex
    #
    vx
    cab
    #
    cuni
    #
    wceq
    #
    @11
    vt
    @40
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    @27
    @34
    @17
    @46
    @34
    @40
    @16
    wcel
    #
    @17
    @46
    @34
    @40
    @3
    wss
    @47
    @34
    vt
    @40
    @3
    @9
    @40
    wcel
    @9
    @37
    wceq
    #
    vy
    @18
    wrex
    #
    @34
    @9
    @3
    wcel
    #
    @39
    @49
    vx
    @9
    vt
    vex
    vx
    vt
    weq
    @38
    @48
    vy
    @18
    @35
    @9
    @37
    eqeq1
    rexbidv
    elab
    @34
    @49
    @9
    @21
    cS
    cin
    #
    wceq
    #
    vd
    cJ
    wrex
    #
    @50
    @34
    @48
    @53
    vy
    @18
    @33
    vy
    vc
    wel
    #
    @48
    @53
    wi
    #
    wi
    #
    @2
    @33
    @18
    cJ
    wss
    #
    @56
    vc
    cJ
    selpw
    @57
    @54
    @55
    @57
    @54
    wa
    @36
    cJ
    wcel
    #
    @55
    @18
    cJ
    @36
    ssel2
    @58
    @48
    @53
    @52
    @48
    vd
    @36
    cJ
    vd
    vy
    weq
    @51
    @37
    @9
    @21
    @36
    cS
    ineq1
    eqeq2d
    rspcev
    ex
    syl
    ex
    sylbi
    adantl
    rexlimdv
    @34
    @0
    @32
    @50
    @53
    wb
    @0
    @1
    @33
    simpll
    @2
    @32
    @33
    @1
    @0
    cS
    cJ
    cuni
    #
    wss
    #
    @32
    cX
    @59
    cS
    cmpsub.1
    sseq2i
    @60
    @0
    @32
    @0
    @60
    @59
    cvv
    wcel
    @32
    cJ
    ctop
    uniexg
    cS
    @59
    cvv
    ssexg
    sylan2
    ancoms
    sylan2b
    adantr
    vd
    @9
    cS
    cJ
    ctop
    cvv
    elrest
    syl2anc
    sylibrd
    syl5bi
    ssrdv
    @40
    @3
    vy
    vx
    @18
    @37
    vc
    vex
    abrexex
    elpw
    sylibr
    @15
    @46
    vs
    @40
    @16
    @6
    @40
    wceq
    #
    @8
    @42
    @14
    @45
    @61
    @7
    @41
    @5
    @6
    @40
    unieq
    eqeq2d
    @61
    @11
    vt
    @13
    @44
    @61
    @12
    @43
    cfn
    @6
    @40
    pweq
    ineq1d
    rexeqdv
    imbi12d
    rspcva
    sylan
    ex
    @34
    @20
    @46
    @26
    @34
    @20
    @46
    @26
    wi
    @34
    @20
    wa
    #
    @46
    cS
    cS
    wceq
    #
    cS
    @10
    wceq
    #
    vt
    @44
    wrex
    #
    wi
    #
    @26
    @62
    @63
    @42
    @65
    @45
    @62
    cS
    @5
    cS
    @41
    @2
    cS
    @5
    wceq
    @33
    @20
    cS
    cJ
    cX
    cmpsub.1
    restuni
    ad2antrr
    #
    @62
    @41
    vy
    @18
    cS
    @36
    cin
    #
    ciun
    #
    cS
    @62
    @41
    vy
    @18
    @37
    ciun
    @69
    vy
    vx
    @18
    @37
    @36
    cS
    vy
    vex
    inex1
    dfiun2
    @62
    vy
    @18
    @37
    @68
    @37
    @68
    wceq
    @62
    @54
    wa
    @36
    cS
    incom
    a1i
    iuneq2dv
    syl5eqr
    @62
    @69
    cS
    vy
    @18
    @36
    ciun
    #
    cin
    #
    cS
    vy
    @18
    cS
    @36
    iunin2
    @62
    @71
    cS
    @19
    cin
    #
    cS
    @62
    @70
    @19
    cS
    @70
    @19
    wceq
    @62
    @19
    @70
    vy
    @18
    uniiun
    eqcomi
    a1i
    ineq2d
    @20
    @72
    cS
    wceq
    @34
    @20
    @72
    @19
    cS
    cin
    #
    cS
    cS
    @19
    incom
    @20
    @73
    cS
    wceq
    cS
    @19
    sseqin2
    biimpi
    syl5eq
    adantl
    eqtrd
    syl5eq
    eqtr2d
    eqeq12d
    @62
    @64
    @11
    vt
    @44
    @62
    cS
    @5
    @10
    @67
    eqeq1d
    rexbidv
    imbi12d
    @66
    @65
    @62
    @26
    @63
    @65
    cS
    eqid
    a1bi
    @62
    @64
    @26
    vt
    @44
    @9
    @44
    wcel
    #
    @62
    @6
    @37
    wceq
    #
    vy
    @18
    wrex
    #
    vs
    @9
    wral
    #
    @9
    cfn
    wcel
    #
    wa
    #
    @64
    @26
    wi
    #
    @74
    @9
    @43
    wcel
    #
    @78
    wa
    @79
    @9
    @43
    cfn
    elin
    @81
    @77
    @78
    @81
    @9
    @40
    wss
    @6
    @40
    wcel
    #
    vs
    @9
    wral
    @77
    vt
    @40
    selpw
    vs
    @9
    @40
    dfss3
    @82
    @76
    vs
    @9
    @39
    @76
    vx
    @6
    vs
    vex
    vx
    vs
    weq
    @38
    @75
    vy
    @18
    @35
    @6
    @37
    eqeq1
    rexbidv
    elab
    ralbii
    3bitri
    anbi1i
    bitri
    @62
    @79
    wa
    #
    @9
    @18
    vf
    cv
    #
    wf
    #
    @6
    @6
    @84
    cfv
    #
    cS
    cin
    #
    wceq
    #
    vs
    @9
    wral
    #
    wa
    #
    vf
    wex
    #
    @80
    @79
    @91
    @62
    @78
    @77
    @91
    @75
    @88
    vs
    vy
    @9
    @18
    vf
    @36
    @86
    wceq
    @37
    @87
    @6
    @36
    @86
    cS
    ineq1
    eqeq2d
    ac6sfi
    ancoms
    adantl
    @83
    @91
    @64
    @84
    crn
    #
    @25
    wcel
    #
    cS
    @92
    cuni
    #
    wss
    #
    wa
    #
    vf
    wex
    #
    @26
    @83
    @64
    @91
    @97
    @83
    @64
    @91
    @97
    wi
    @83
    @64
    wa
    #
    @90
    @96
    vf
    @98
    @90
    @96
    @98
    @90
    wa
    #
    @93
    @95
    @99
    @24
    cfn
    @92
    @99
    @92
    @18
    wss
    #
    @92
    @24
    wcel
    @85
    @100
    @98
    @89
    @9
    @18
    @84
    frn
    ad2antrl
    @92
    @18
    @84
    vf
    vex
    rnex
    elpw
    sylibr
    @99
    @78
    @92
    @9
    cdom
    wbr
    #
    @92
    cfn
    wcel
    @83
    @78
    @64
    @90
    @62
    @77
    @78
    simprr
    ad2antrr
    @83
    @85
    @101
    @64
    @89
    @79
    @85
    @101
    @62
    @78
    @85
    @101
    @77
    @85
    @78
    @9
    @92
    @84
    wfo
    #
    @101
    @85
    @84
    @9
    wfn
    #
    @102
    @9
    @18
    @84
    ffn
    #
    @9
    @84
    dffn4
    sylib
    @9
    @92
    @84
    fodomfi
    sylan2
    adantll
    adantll
    ad2ant2r
    @9
    @92
    domfi
    syl2anc
    elind
    @99
    @95
    @10
    @94
    wss
    #
    @90
    @105
    @98
    @90
    vw
    @10
    @94
    @90
    vw
    vu
    wel
    #
    vu
    vt
    wel
    #
    wa
    #
    vu
    wex
    vw
    vv
    wel
    #
    vv
    cv
    #
    @92
    wcel
    #
    wa
    #
    vv
    wex
    #
    vw
    cv
    #
    @10
    wcel
    @114
    @94
    wcel
    @90
    @108
    @113
    vu
    @90
    @108
    @114
    vu
    cv
    #
    @84
    cfv
    #
    wcel
    #
    @116
    @92
    wcel
    #
    wa
    #
    @113
    @89
    @85
    @107
    @115
    @116
    cS
    cin
    #
    wceq
    #
    wi
    #
    @108
    @119
    wi
    #
    @88
    @121
    vs
    @115
    @9
    vs
    vu
    weq
    #
    @6
    @115
    @87
    @120
    @124
    id
    @124
    @86
    @116
    cS
    @6
    @115
    @84
    fveq2
    ineq1d
    eqeq12d
    rspccv
    @122
    @85
    @123
    @108
    @122
    @85
    @119
    @106
    @107
    @122
    @85
    @119
    wi
    #
    wi
    @107
    @122
    @106
    @125
    @107
    @122
    @121
    @106
    @125
    wi
    @107
    @121
    pm2.27
    @107
    @121
    @106
    @125
    @107
    @121
    @106
    w3a
    #
    @85
    @117
    @118
    @107
    @121
    @106
    @85
    @117
    wi
    #
    @121
    @106
    @127
    wi
    #
    wi
    @107
    @121
    @115
    @116
    wss
    #
    @128
    @121
    @129
    @120
    @116
    wss
    @116
    cS
    inss1
    @115
    @120
    @116
    sseq1
    mpbiri
    @129
    @106
    @117
    @85
    @115
    @116
    @114
    ssel
    a1dd
    syl
    a1i
    3imp
    @85
    @103
    @126
    @118
    @104
    @107
    @121
    @103
    @118
    wi
    @106
    @103
    @107
    @118
    @9
    @115
    @84
    fnfvelrn
    expcom
    3ad2ant1
    syl5
    jcad
    3exp
    syld
    com3r
    imp
    com3l
    impcom
    sylan2
    @112
    @119
    vv
    @116
    @115
    @84
    fvex
    @110
    @116
    wceq
    @109
    @117
    @111
    @118
    @110
    @116
    @114
    eleq2
    @110
    @116
    @92
    eleq1
    anbi12d
    spcev
    syl6
    exlimdv
    vu
    @114
    @9
    eluni
    vv
    @114
    @92
    eluni
    3imtr4g
    ssrdv
    adantl
    @64
    @95
    @105
    wb
    @83
    @90
    cS
    @10
    @94
    sseq1
    ad2antlr
    mpbird
    jca
    ex
    eximdv
    ex
    com23
    @96
    @26
    vf
    @23
    @95
    vd
    @92
    @25
    @21
    @92
    wceq
    @22
    @94
    cS
    @21
    @92
    unieq
    sseq2d
    rspcev
    exlimiv
    syl8
    mpd
    sylan2b
    rexlimdva
    syl5bir
    sylbird
    ex
    com23
    syld
    ralrimdva
    vt
    cS
    cJ
    cX
    vs
    vc
    vd
    cmpsub.1
    cmpsublem
    impbid
    bitrd
end
