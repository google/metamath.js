include "cab.mm"
include "wcel.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "c0.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "ccom.mm"
include "csn.mm"
include "cxp.mm"
include "cid.mm"
include "cres.mm"
include "coass.mm"
include "ccnv.mm"
include "df1o2.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "0ex.mm"
include "eqid.mm"
include "mapsncnv.mm"
include "coeq2i.mm"
include "wf1o.mm"
include "wceq.mm"
include "mapsnf1o2.mm"
include "f1ococnv2.mm"
include "mp1i.mm"
include "syl5eqr.mm"
include "coeq2d.mm"
include "syl5eq.mm"
include "wf.mm"
include "pf1f.mm"
include "fcoi1.mm"
include "3syl.mm"
include "eqtrd.mm"
include "cof.mm"
include "cevl.mm"
include "crn.mm"
include "ces.mm"
include "evlval.mm"
include "rneqi.mm"
include "wa.mm"
include "an4.mm"
include "wi.mm"
include "mpfpf1.mm"
include "vex.mm"
include "elab.mm"
include "eleq1.mm"
include "syl5bbr.mm"
include "anbi1d.mm"
include "ovex.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "expcom.mm"
include "an4s.mm"
include "expimpd.mm"
include "vtocl2ga.mm"
include "syl2an.mm"
include "expcomd.mm"
include "impcom.mm"
include "wfn.mm"
include "mpff.mm"
include "ad2antrl.mm"
include "ffn.mm"
include "syl.mm"
include "ad2antll.mm"
include "mapsnf1o3.mm"
include "f1of.mm"
include "ovexd.mm"
include "a1i.mm"
include "inidm.mm"
include "ofco.mm"
include "sylibrd.mm"
include "syl5bi.mm"
include "imp.mm"
include "coeq1.mm"
include "weq.mm"
include "cpl1.mm"
include "cascl.mm"
include "ce1.mm"
include "ccrg.mm"
include "cmpl.mm"
include "pf1rcl.mm"
include "adantr.mm"
include "crh.mm"
include "csca.mm"
include "casa.mm"
include "con0.mm"
include "1on.mm"
include "mplassa.mm"
include "sylancr.mm"
include "ply1ascl.mm"
include "asclrhm.mm"
include "mplsca.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"
include "rhmf.mm"
include "ffvelrnda.mm"
include "evl1val.mm"
include "syl2anc.mm"
include "evl1sca.mm"
include "sylan.mm"
include "cress.mm"
include "ressid.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "csubrg.mm"
include "crg.mm"
include "crngring.mm"
include "subrgid.mm"
include "simpr.mm"
include "evlssca.mm"
include "eqtr3d.mm"
include "coeq1d.mm"
include "3eqtr3d.mm"
include "wral.mm"
include "snex.mm"
include "xpex.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "rspccva.mm"
include "eqeltrrd.mm"
include "resiexg.mm"
include "ax-mp.mm"
include "eqeltrd.mm"
include "el1o.mm"
include "fveq2.mm"
include "sylbi.mm"
include "mpteq2dv.mm"
include "syl5ibrcom.mm"
include "pf1mpf.mm"
include "mpfind.mm"
include "wb.mm"
include "elabg.mm"
include "mpbid.mm"

theorem pf1ind
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let vw: setvar w
  assume pf1ind.cb: |- B = ( Base ` R )
  assume pf1ind.cp: |- .+ = ( +g ` R )
  assume pf1ind.ct: |- .x. = ( .r ` R )
  assume pf1ind.cq: |- Q = ran ( eval1 ` R )
  assume pf1ind.ad: |- ( ( ph /\ ( ( f e. Q /\ ta ) /\ ( g e. Q /\ et ) ) ) -> ze )
  assume pf1ind.mu: |- ( ( ph /\ ( ( f e. Q /\ ta ) /\ ( g e. Q /\ et ) ) ) -> si )
  assume pf1ind.wa: |- ( x = ( B X. { f } ) -> ( ps <-> ch ) )
  assume pf1ind.wb: |- ( x = ( _I |` B ) -> ( ps <-> th ) )
  assume pf1ind.wc: |- ( x = f -> ( ps <-> ta ) )
  assume pf1ind.wd: |- ( x = g -> ( ps <-> et ) )
  assume pf1ind.we: |- ( x = ( f oF .+ g ) -> ( ps <-> ze ) )
  assume pf1ind.wf: |- ( x = ( f oF .x. g ) -> ( ps <-> si ) )
  assume pf1ind.wg: |- ( x = A -> ( ps <-> rh ) )
  assume pf1ind.co: |- ( ( ph /\ f e. B ) -> ch )
  assume pf1ind.pr: |- ( ph -> th )
  assume pf1ind.a: |- ( ph -> A e. Q )

  disjoint f g
  disjoint f x
  disjoint .+ f
  disjoint g x
  disjoint .+ g
  disjoint .+ x
  disjoint B f
  disjoint B g
  disjoint B x
  disjoint et f
  disjoint et x
  disjoint f ph
  disjoint g ph
  disjoint A x
  disjoint ch x
  disjoint f ps
  disjoint g ps
  disjoint Q f
  disjoint Q g
  disjoint rh x
  disjoint si x
  disjoint ta x
  disjoint th x
  disjoint .x. f
  disjoint .x. g
  disjoint .x. x
  disjoint x ze
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint a y
  disjoint .+ a
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint .+ b
  disjoint f y
  disjoint g y
  disjoint x y
  disjoint .+ y
  disjoint a w
  disjoint B a
  disjoint b w
  disjoint B b
  disjoint f w
  disjoint g w
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint B y
  disjoint a ph
  disjoint b ph
  disjoint A b
  disjoint A y
  disjoint a ps
  disjoint b ps
  disjoint ps y
  disjoint Q b
  disjoint R a
  disjoint R b
  disjoint R w
  disjoint .x. a
  disjoint .x. b
  disjoint .x. y
  assert |- ( ph -> rh )

  proof
    wph
    cA
    wps
    vx
    cab
    #
    wcel
    #
    wrh
    wph
    cA
    vb
    cB
    c1o
    cmap
    co
    #
    c0
    vb
    cv
    #
    cfv
    #
    cmpt
    #
    ccom
    #
    vw
    cB
    c1o
    vw
    cv
    csn
    cxp
    cmpt
    #
    ccom
    #
    cA
    @0
    wph
    @8
    cA
    cid
    cB
    cres
    #
    ccom
    #
    cA
    wph
    @8
    cA
    @5
    @7
    ccom
    #
    ccom
    @10
    cA
    @5
    @7
    coass
    wph
    @11
    @9
    cA
    wph
    @11
    @5
    @5
    ccnv
    #
    ccom
    #
    @9
    @12
    @7
    @5
    vb
    vw
    cB
    c1o
    @5
    c0
    df1o2
    cB
    cR
    cbs
    cfv
    cvv
    pf1ind.cb
    cR
    cbs
    fvex
    eqeltri
    #
    0ex
    @5
    eqid
    #
    mapsncnv
    coeq2i
    @2
    cB
    @5
    wf1o
    @13
    @9
    wceq
    wph
    vb
    cB
    c1o
    @5
    c0
    df1o2
    @14
    0ex
    @15
    mapsnf1o2
    @2
    cB
    @5
    f1ococnv2
    mp1i
    syl5eqr
    #
    coeq2d
    syl5eq
    wph
    cA
    cQ
    wcel
    #
    cB
    cB
    cA
    wf
    @10
    cA
    wceq
    pf1ind.a
    cB
    cQ
    cR
    cA
    pf1ind.cq
    pf1ind.cb
    pf1f
    cB
    cB
    cA
    fcoi1
    3syl
    eqtrd
    wph
    vy
    cv
    #
    @7
    ccom
    #
    @0
    wcel
    @2
    va
    cv
    #
    csn
    #
    cxp
    #
    @7
    ccom
    #
    @0
    wcel
    vb
    @2
    @20
    @3
    cfv
    #
    cmpt
    #
    @7
    ccom
    #
    @0
    wcel
    #
    @20
    @7
    ccom
    #
    @0
    wcel
    #
    @3
    @7
    ccom
    #
    @0
    wcel
    #
    @20
    @3
    c.pl
    cof
    #
    co
    #
    @7
    ccom
    #
    @0
    wcel
    #
    @20
    @3
    c.x
    cof
    #
    co
    #
    @7
    ccom
    #
    @0
    wcel
    #
    @8
    @0
    wcel
    vy
    @6
    cB
    c.pl
    c1o
    cR
    cevl
    co
    #
    crn
    #
    cB
    cR
    c.x
    va
    vb
    c1o
    pf1ind.cb
    pf1ind.cp
    pf1ind.ct
    @40
    cB
    c1o
    cR
    ces
    co
    cfv
    cB
    @40
    cR
    c1o
    @40
    eqid
    #
    pf1ind.cb
    evlval
    #
    rneqi
    #
    wph
    @20
    @41
    wcel
    #
    @29
    wa
    @3
    @41
    wcel
    #
    @31
    wa
    wa
    #
    @35
    @47
    @45
    @46
    wa
    #
    @29
    @31
    wa
    #
    wa
    #
    wph
    @35
    @45
    @29
    @46
    @31
    an4
    #
    wph
    @48
    @49
    @35
    wph
    @48
    wa
    #
    @49
    @28
    @30
    @32
    co
    #
    @0
    wcel
    #
    @35
    @48
    wph
    @49
    @54
    wi
    @48
    @49
    wph
    @54
    @45
    @28
    cQ
    wcel
    #
    @30
    cQ
    wcel
    #
    @49
    wph
    wa
    #
    @54
    wi
    #
    @46
    vw
    cB
    cQ
    cR
    @41
    @20
    pf1ind.cq
    pf1ind.cb
    @41
    eqid
    #
    mpfpf1
    #
    vw
    cB
    cQ
    cR
    @41
    @3
    pf1ind.cq
    pf1ind.cb
    @59
    mpfpf1
    #
    wta
    wet
    wa
    #
    wph
    wa
    #
    wze
    wi
    @29
    wet
    wa
    #
    wph
    wa
    #
    @28
    vg
    cv
    #
    @32
    co
    #
    @0
    wcel
    #
    wi
    @58
    vf
    vg
    @28
    @30
    cQ
    cQ
    vf
    cv
    #
    @28
    wceq
    #
    @63
    @65
    wze
    @68
    @70
    @62
    @64
    wph
    @70
    wta
    @29
    wet
    wta
    @69
    @0
    wcel
    @70
    @29
    wps
    wta
    vx
    @69
    vf
    vex
    pf1ind.wc
    elab
    @69
    @28
    @0
    eleq1
    syl5bbr
    anbi1d
    anbi1d
    #
    wze
    @69
    @66
    @32
    co
    #
    @0
    wcel
    @70
    @68
    wps
    wze
    vx
    @72
    @69
    @66
    @32
    ovex
    pf1ind.we
    elab
    @70
    @72
    @67
    @0
    @69
    @28
    @66
    @32
    oveq1
    eleq1d
    syl5bbr
    imbi12d
    @66
    @30
    wceq
    #
    @65
    @57
    @68
    @54
    @73
    @64
    @49
    wph
    @73
    wet
    @31
    @29
    wet
    @66
    @0
    wcel
    @73
    @31
    wps
    wet
    vx
    @66
    vg
    vex
    pf1ind.wd
    elab
    @66
    @30
    @0
    eleq1
    syl5bbr
    anbi2d
    anbi1d
    #
    @73
    @67
    @53
    @0
    @66
    @30
    @28
    @32
    oveq2
    eleq1d
    imbi12d
    @69
    cQ
    wcel
    #
    @66
    cQ
    wcel
    #
    wa
    #
    @62
    wph
    wze
    @75
    wta
    @76
    wet
    wph
    wze
    wi
    wph
    @75
    wta
    wa
    @76
    wet
    wa
    wa
    #
    wze
    pf1ind.ad
    expcom
    an4s
    expimpd
    vtocl2ga
    syl2an
    expcomd
    impcom
    @52
    @34
    @53
    @0
    @52
    @2
    @2
    @2
    cB
    c.pl
    @20
    @3
    @7
    cvv
    cvv
    cvv
    @52
    @2
    cB
    @20
    wf
    #
    @20
    @2
    wfn
    @45
    @79
    wph
    @46
    cB
    @41
    cB
    cR
    @20
    c1o
    @44
    pf1ind.cb
    mpff
    ad2antrl
    @2
    cB
    @20
    ffn
    syl
    #
    @52
    @2
    cB
    @3
    wf
    #
    @3
    @2
    wfn
    @46
    @81
    wph
    @45
    cB
    @41
    cB
    cR
    @3
    c1o
    @44
    pf1ind.cb
    mpff
    ad2antll
    @2
    cB
    @3
    ffn
    syl
    #
    cB
    @2
    @7
    wf1o
    cB
    @2
    @7
    wf
    @52
    vw
    cB
    c1o
    @7
    c0
    df1o2
    @14
    0ex
    @7
    eqid
    mapsnf1o3
    cB
    @2
    @7
    f1of
    mp1i
    #
    @52
    cB
    c1o
    cmap
    ovexd
    #
    @84
    cB
    cvv
    wcel
    #
    @52
    @14
    a1i
    #
    @2
    inidm
    #
    ofco
    eleq1d
    sylibrd
    expimpd
    syl5bi
    imp
    wph
    @47
    @39
    @47
    @50
    wph
    @39
    @51
    wph
    @48
    @49
    @39
    @52
    @49
    @28
    @30
    @36
    co
    #
    @0
    wcel
    #
    @39
    @48
    wph
    @49
    @89
    wi
    @48
    @49
    wph
    @89
    @45
    @55
    @56
    @57
    @89
    wi
    #
    @46
    @60
    @61
    @63
    wsi
    wi
    @65
    @28
    @66
    @36
    co
    #
    @0
    wcel
    #
    wi
    @90
    vf
    vg
    @28
    @30
    cQ
    cQ
    @70
    @63
    @65
    wsi
    @92
    @71
    wsi
    @69
    @66
    @36
    co
    #
    @0
    wcel
    @70
    @92
    wps
    wsi
    vx
    @93
    @69
    @66
    @36
    ovex
    pf1ind.wf
    elab
    @70
    @93
    @91
    @0
    @69
    @28
    @66
    @36
    oveq1
    eleq1d
    syl5bbr
    imbi12d
    @73
    @65
    @57
    @92
    @89
    @74
    @73
    @91
    @88
    @0
    @66
    @30
    @28
    @36
    oveq2
    eleq1d
    imbi12d
    @77
    @62
    wph
    wsi
    @75
    wta
    @76
    wet
    wph
    wsi
    wi
    wph
    @78
    wsi
    pf1ind.mu
    expcom
    an4s
    expimpd
    vtocl2ga
    syl2an
    expcomd
    impcom
    @52
    @38
    @88
    @0
    @52
    @2
    @2
    @2
    cB
    c.x
    @20
    @3
    @7
    cvv
    cvv
    cvv
    @80
    @82
    @83
    @84
    @84
    @86
    @87
    ofco
    eleq1d
    sylibrd
    expimpd
    syl5bi
    imp
    @18
    @22
    wceq
    @19
    @23
    @0
    @18
    @22
    @7
    coeq1
    eleq1d
    @18
    @25
    wceq
    @19
    @26
    @0
    @18
    @25
    @7
    coeq1
    eleq1d
    vy
    va
    weq
    @19
    @28
    @0
    @18
    @20
    @7
    coeq1
    eleq1d
    vy
    vb
    weq
    @19
    @30
    @0
    @18
    @3
    @7
    coeq1
    eleq1d
    @18
    @33
    wceq
    @19
    @34
    @0
    @18
    @33
    @7
    coeq1
    eleq1d
    @18
    @37
    wceq
    @19
    @38
    @0
    @18
    @37
    @7
    coeq1
    eleq1d
    @18
    @6
    wceq
    @19
    @8
    @0
    @18
    @6
    @7
    coeq1
    eleq1d
    wph
    @20
    cB
    wcel
    #
    wa
    #
    cB
    @21
    cxp
    #
    @23
    @0
    @95
    @20
    cR
    cpl1
    cfv
    #
    cascl
    cfv
    #
    cfv
    #
    cR
    ce1
    cfv
    #
    cfv
    #
    @99
    @40
    cfv
    #
    @7
    ccom
    #
    @96
    @23
    @95
    cR
    ccrg
    wcel
    #
    @99
    c1o
    cR
    cmpl
    co
    #
    cbs
    cfv
    #
    wcel
    @101
    @103
    wceq
    wph
    @104
    @94
    wph
    @17
    @104
    pf1ind.a
    cQ
    cR
    cA
    pf1ind.cq
    pf1rcl
    syl
    #
    adantr
    #
    wph
    cB
    @106
    @20
    @98
    wph
    @98
    cR
    @105
    crh
    co
    #
    wcel
    cB
    @106
    @98
    wf
    wph
    @98
    @105
    csca
    cfv
    #
    @105
    crh
    co
    #
    @109
    wph
    @105
    casa
    wcel
    #
    @98
    @111
    wcel
    wph
    c1o
    con0
    wcel
    #
    @104
    @112
    1on
    @107
    @105
    cR
    c1o
    con0
    @105
    eqid
    #
    mplassa
    sylancr
    @98
    @110
    @105
    @98
    @97
    cR
    @97
    eqid
    #
    @98
    eqid
    #
    ply1ascl
    #
    @110
    eqid
    asclrhm
    syl
    wph
    cR
    @110
    @105
    crh
    wph
    @105
    cR
    c1o
    con0
    ccrg
    @114
    @113
    wph
    1on
    a1i
    @107
    mplsca
    oveq1d
    eleqtrrd
    cB
    @106
    cR
    @105
    @98
    pf1ind.cb
    @106
    eqid
    #
    rhmf
    syl
    ffvelrnda
    vw
    @99
    cB
    @40
    cR
    @106
    @105
    @100
    @100
    eqid
    #
    @42
    pf1ind.cb
    @114
    @118
    evl1val
    syl2anc
    wph
    @104
    @94
    @101
    @96
    wceq
    @107
    @98
    cB
    @97
    cR
    @100
    @20
    @119
    @115
    pf1ind.cb
    @116
    evl1sca
    sylan
    @95
    @102
    @22
    @7
    @95
    @20
    c1o
    cR
    cB
    cress
    co
    #
    cmpl
    co
    #
    cascl
    cfv
    #
    cfv
    #
    @40
    cfv
    @102
    @22
    @95
    @123
    @99
    @40
    @95
    @20
    @122
    @98
    @95
    @122
    @105
    cascl
    cfv
    @98
    @95
    @121
    @105
    cascl
    @95
    @120
    cR
    c1o
    cmpl
    @95
    @104
    @120
    cR
    wceq
    @108
    cB
    cR
    ccrg
    pf1ind.cb
    ressid
    syl
    oveq2d
    fveq2d
    @117
    syl6eqr
    fveq1d
    fveq2d
    @95
    @122
    cB
    @40
    cB
    cR
    @120
    c1o
    con0
    @121
    @20
    @43
    @121
    eqid
    @120
    eqid
    pf1ind.cb
    @122
    eqid
    @113
    @95
    1on
    a1i
    @108
    wph
    cB
    cR
    csubrg
    cfv
    wcel
    #
    @94
    wph
    @104
    cR
    crg
    wcel
    @124
    @107
    cR
    crngring
    cB
    cR
    pf1ind.cb
    subrgid
    3syl
    adantr
    wph
    @94
    simpr
    evlssca
    eqtr3d
    coeq1d
    3eqtr3d
    wph
    cB
    @69
    csn
    #
    cxp
    #
    @0
    wcel
    #
    vf
    cB
    wral
    @94
    @96
    @0
    wcel
    #
    wph
    @127
    vf
    cB
    wph
    @69
    cB
    wcel
    wa
    wch
    @127
    pf1ind.co
    wps
    wch
    vx
    @126
    cB
    @125
    @14
    @69
    snex
    xpex
    pf1ind.wa
    elab
    sylibr
    ralrimiva
    @127
    @128
    vf
    @20
    cB
    vf
    va
    weq
    #
    @126
    @96
    @0
    @129
    @125
    @21
    cB
    @69
    @20
    sneq
    xpeq2d
    eleq1d
    rspccva
    sylan
    eqeltrrd
    wph
    @20
    c1o
    wcel
    #
    @27
    wph
    @27
    @130
    @11
    @0
    wcel
    wph
    @11
    @9
    @0
    @16
    wph
    wth
    @9
    @0
    wcel
    pf1ind.pr
    wps
    wth
    vx
    @9
    @85
    @9
    cvv
    wcel
    @14
    cB
    cvv
    resiexg
    ax-mp
    pf1ind.wb
    elab
    sylibr
    eqeltrd
    @130
    @26
    @11
    @0
    @130
    @25
    @5
    @7
    @130
    vb
    @2
    @24
    @4
    @130
    @20
    c0
    wceq
    @24
    @4
    wceq
    @20
    el1o
    @20
    c0
    @3
    fveq2
    sylbi
    mpteq2dv
    coeq1d
    eleq1d
    syl5ibrcom
    imp
    wph
    @17
    @6
    @41
    wcel
    pf1ind.a
    vb
    cB
    cQ
    cR
    @41
    cA
    pf1ind.cq
    pf1ind.cb
    @59
    pf1mpf
    syl
    mpfind
    eqeltrrd
    wph
    @17
    @1
    wrh
    wb
    pf1ind.a
    wps
    wrh
    vx
    cA
    cQ
    pf1ind.wg
    elabg
    syl
    mpbid
end
