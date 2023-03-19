include "cv.mm"
include "crn.mm"
include "cres.mm"
include "wf1o.mm"
include "cpw.mm"
include "wrex.mm"
include "wcel.mm"
include "wss.mm"
include "wbr.mm"
include "wn.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wral.mm"
include "crio.mm"
include "wa.mm"
include "cdm.mm"
include "cnvimass.mm"
include "a1i.mm"
include "wceq.mm"
include "wfn.mm"
include "fndm.mm"
include "syl.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "wreu.mm"
include "wwe.mm"
include "cvv.mm"
include "c0.mm"
include "wne.mm"
include "syl5sseq.mm"
include "ssexg.mm"
include "syl2anc.mm"
include "inisegn0.mm"
include "biimpi.mm"
include "adantl.mm"
include "wereu.mm"
include "syl13anc.mm"
include "riotacl.mm"
include "sseldd.mm"
include "ralrimiva.mm"
include "cmpt.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "raleqdv.mm"
include "riotaeqbidv.mm"
include "wb.mm"
include "breq1.mm"
include "notbid.mm"
include "cbvralv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "bitrd.mm"
include "cbvriotav.mm"
include "eqtrd.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "rnmptss.mm"
include "ssexd.mm"
include "elpwg.mm"
include "mpbird.mm"
include "wf1.mm"
include "wfo.mm"
include "wf.mm"
include "cfv.mm"
include "wi.mm"
include "dffn3.mm"
include "fssresd.mm"
include "simpl.mm"
include "simprl.mm"
include "simprr.mm"
include "w3a.mm"
include "fvres.mm"
include "eqcomd.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "ad2antlr.mm"
include "3eqtrd.mm"
include "3adantl1.mm"
include "simpl1.mm"
include "simpl3.mm"
include "vex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "3ad2antl2.mm"
include "sylibr.mm"
include "id.mm"
include "eleq1.mm"
include "3anbi3d.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "3anbi2d.mm"
include "eqeq1d.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfrn.mm"
include "nfel.mm"
include "nfcri.mm"
include "nf3an.mm"
include "nfan.mm"
include "simp3.mm"
include "simp11.mm"
include "simp2.mm"
include "eqtr2d.mm"
include "3ad2ant3.mm"
include "cbvreuv.mm"
include "sylib.mm"
include "riota1.mm"
include "3adant3.mm"
include "simpld.mm"
include "syl3anc.mm"
include "riota2.mm"
include "3adant1r.mm"
include "sselda.mm"
include "3adant2.mm"
include "3ad2ant1.mm"
include "fniniseg.mm"
include "3syl.mm"
include "mpbid.mm"
include "simprd.mm"
include "jca.mm"
include "rspa.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "chvarv.mm"
include "syl31anc.mm"
include "wor.mm"
include "weso.mm"
include "3ad2antl1.mm"
include "sotrieq2.mm"
include "syl12anc.mm"
include "ex.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "riotaex.mm"
include "rgenw.mm"
include "fnmpt.mm"
include "ffvelrnda.mm"
include "fvmpt2.mm"
include "eqeltrd.mm"
include "fvex.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "vtocl.mm"
include "rspcev.mm"
include "dffo3.mm"
include "df-f1o.mm"
include "nfriota1.mm"
include "nfmpt.mm"
include "nfres.mm"
include "nff1o.mm"
include "reseq2.mm"
include "eqidd.mm"
include "f1oeq123d.mm"
include "rspce.mm"
include "cbvrexv.mm"

theorem wessf1ornlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G
  let cV: class V
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let va: setvar a
  let vb: setvar b
  assume wessf1ornlem.f: |- ( ph -> F Fn A )
  assume wessf1ornlem.a: |- ( ph -> A e. V )
  assume wessf1ornlem.r: |- ( ph -> R We A )
  assume wessf1ornlem.g: |- G = ( y e. ran F |-> ( iota_ x e. ( `' F " { y } ) A. z e. ( `' F " { y } ) -. z R x ) )

  disjoint A x
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint u v
  disjoint u w
  disjoint v w
  disjoint t x
  disjoint u x
  disjoint v x
  disjoint F a
  disjoint F b
  disjoint F t
  disjoint F w
  disjoint a b
  disjoint a t
  disjoint a w
  disjoint b t
  disjoint b w
  disjoint F u
  disjoint F v
  disjoint t y
  disjoint t z
  disjoint u y
  disjoint u z
  disjoint v y
  disjoint v z
  disjoint G a
  disjoint G b
  disjoint G t
  disjoint G w
  disjoint G u
  disjoint G v
  disjoint R a
  disjoint R b
  disjoint R t
  disjoint R w
  disjoint R u
  disjoint R v
  disjoint a ph
  disjoint b ph
  disjoint ph t
  disjoint ph w
  disjoint ph u
  assert |- ( ph -> E. x e. ~P A ( F |` x ) : x -1-1-onto-> ran F )

  proof
    wph
    vv
    cv
    #
    cF
    crn
    #
    cF
    @0
    cres
    #
    wf1o
    #
    vv
    cA
    cpw
    #
    wrex
    #
    vx
    cv
    #
    @1
    cF
    @6
    cres
    #
    wf1o
    #
    vx
    @4
    wrex
    wph
    cG
    crn
    #
    @4
    wcel
    #
    @9
    @1
    cF
    @9
    cres
    #
    wf1o
    #
    @5
    wph
    @10
    @9
    cA
    wss
    #
    wph
    vt
    cv
    #
    @0
    cR
    wbr
    #
    wn
    #
    vt
    cF
    ccnv
    #
    vu
    cv
    #
    csn
    #
    cima
    #
    wral
    #
    vv
    @20
    crio
    #
    cA
    wcel
    #
    vu
    @1
    wral
    @13
    wph
    @23
    vu
    @1
    wph
    @18
    @1
    wcel
    #
    wa
    #
    @20
    cA
    @22
    @25
    @20
    cF
    cdm
    #
    cA
    @20
    @26
    wss
    @25
    cF
    @19
    cnvimass
    #
    a1i
    wph
    @26
    cA
    wceq
    #
    @24
    wph
    cF
    cA
    wfn
    #
    @28
    wessf1ornlem.f
    cA
    cF
    fndm
    syl
    #
    adantr
    sseqtrd
    #
    @25
    @21
    vv
    @20
    wreu
    #
    @22
    @20
    wcel
    @25
    cA
    cR
    wwe
    #
    @20
    cvv
    wcel
    #
    @20
    cA
    wss
    #
    @20
    c0
    wne
    #
    @32
    wph
    @33
    @24
    wessf1ornlem.r
    adantr
    wph
    @34
    @24
    wph
    @35
    cA
    cV
    wcel
    @34
    wph
    @26
    @20
    cA
    @27
    @30
    syl5sseq
    wessf1ornlem.a
    @20
    cA
    cV
    ssexg
    syl2anc
    adantr
    @31
    @24
    @36
    wph
    @24
    @36
    @18
    cF
    inisegn0
    #
    biimpi
    adantl
    #
    vv
    vt
    cA
    @20
    cR
    cvv
    wereu
    syl13anc
    #
    @21
    vv
    @20
    riotacl
    syl
    #
    sseldd
    ralrimiva
    vu
    @1
    @22
    cA
    cG
    cG
    vy
    @1
    vz
    cv
    #
    @6
    cR
    wbr
    #
    wn
    #
    vz
    @17
    vy
    cv
    #
    csn
    #
    cima
    #
    wral
    #
    vx
    @46
    crio
    #
    cmpt
    vu
    @1
    @22
    cmpt
    #
    wessf1ornlem.g
    vy
    vu
    @1
    @48
    @22
    @44
    @18
    wceq
    #
    @48
    @43
    vz
    @20
    wral
    #
    vx
    @20
    crio
    #
    @22
    @50
    @47
    @51
    vx
    @46
    @20
    @50
    @45
    @19
    @17
    @44
    @18
    sneq
    imaeq2d
    #
    @50
    @43
    vz
    @46
    @20
    @53
    raleqdv
    riotaeqbidv
    @52
    @22
    wceq
    @50
    @51
    @21
    vx
    vv
    @20
    @6
    @0
    wceq
    #
    @51
    @14
    @6
    cR
    wbr
    #
    wn
    #
    vt
    @20
    wral
    #
    @21
    @51
    @57
    wb
    @54
    @43
    @56
    vz
    vt
    @20
    @41
    @14
    wceq
    @42
    @55
    @41
    @14
    @6
    cR
    breq1
    notbid
    cbvralv
    a1i
    @54
    @56
    @16
    vt
    @20
    @54
    @55
    @15
    @6
    @0
    @14
    cR
    breq2
    notbid
    ralbidv
    bitrd
    cbvriotav
    a1i
    eqtrd
    cbvmptv
    eqtri
    #
    rnmptss
    syl
    #
    wph
    @9
    cvv
    wcel
    @10
    @13
    wb
    wph
    @9
    cA
    cV
    wessf1ornlem.a
    @59
    ssexd
    @9
    cA
    cvv
    elpwg
    syl
    mpbird
    wph
    @9
    @1
    @11
    wf1
    #
    @9
    @1
    @11
    wfo
    #
    wa
    @12
    wph
    @60
    @61
    wph
    @9
    @1
    @11
    wf
    #
    vw
    cv
    #
    @11
    cfv
    #
    @14
    @11
    cfv
    #
    wceq
    #
    @63
    @14
    wceq
    #
    wi
    #
    vt
    @9
    wral
    vw
    @9
    wral
    #
    wa
    @60
    wph
    @62
    @69
    wph
    cA
    @1
    @9
    cF
    wph
    @29
    cA
    @1
    cF
    wf
    #
    wessf1ornlem.f
    @29
    @70
    cA
    cF
    dffn3
    biimpi
    syl
    @59
    fssresd
    #
    wph
    @68
    vw
    vt
    @9
    @9
    wph
    @63
    @9
    wcel
    #
    @14
    @9
    wcel
    #
    wa
    #
    wa
    wph
    @72
    @73
    @68
    wph
    @74
    simpl
    wph
    @72
    @73
    simprl
    wph
    @72
    @73
    simprr
    wph
    @72
    @73
    w3a
    #
    @66
    @67
    @75
    @66
    wa
    @75
    @63
    cF
    cfv
    #
    @14
    cF
    cfv
    #
    wceq
    #
    @67
    @75
    @66
    simpl
    @72
    @73
    @66
    @78
    wph
    @74
    @66
    wa
    @76
    @64
    @65
    @77
    @72
    @76
    @64
    wceq
    @73
    @66
    @72
    @64
    @76
    @63
    @9
    cF
    fvres
    eqcomd
    ad2antrr
    @74
    @66
    simpr
    @73
    @65
    @77
    wceq
    @72
    @66
    @14
    @9
    cF
    fvres
    ad2antlr
    3eqtrd
    3adantl1
    @75
    @78
    wa
    #
    @67
    @63
    @14
    cR
    wbr
    #
    wn
    #
    @14
    @63
    cR
    wbr
    #
    wn
    #
    wa
    #
    @79
    @81
    @83
    @79
    wph
    @73
    @72
    @77
    @76
    wceq
    #
    @81
    wph
    @72
    @73
    @78
    simpl1
    wph
    @72
    @73
    @78
    simpl3
    @79
    @63
    @22
    wceq
    #
    vu
    @1
    wrex
    #
    @72
    @72
    wph
    @78
    @87
    @73
    @72
    @87
    @78
    @72
    @87
    @63
    cvv
    wcel
    @72
    @87
    wb
    vw
    vex
    vu
    @1
    @22
    @63
    cG
    cvv
    @58
    elrnmpt
    ax-mp
    #
    biimpi
    adantr
    3ad2antl2
    #
    @88
    sylibr
    @78
    @85
    @75
    @78
    @76
    @77
    @78
    id
    eqcomd
    #
    adantl
    wph
    @73
    vb
    cv
    #
    @9
    wcel
    #
    w3a
    #
    @77
    @91
    cF
    cfv
    #
    wceq
    #
    wa
    #
    @91
    @14
    cR
    wbr
    #
    wn
    #
    wi
    #
    wph
    @73
    @72
    w3a
    #
    @85
    wa
    #
    @81
    wi
    vb
    vw
    @91
    @63
    wceq
    #
    @96
    @101
    @98
    @81
    @102
    @93
    @100
    @95
    @85
    @102
    @92
    @72
    wph
    @73
    @91
    @63
    @9
    eleq1
    3anbi3d
    @102
    @94
    @76
    @77
    @91
    @63
    cF
    fveq2
    eqeq2d
    anbi12d
    @102
    @97
    @80
    @91
    @63
    @14
    cR
    breq1
    notbid
    imbi12d
    wph
    va
    cv
    #
    @9
    wcel
    #
    @92
    w3a
    #
    @103
    cF
    cfv
    #
    @94
    wceq
    #
    wa
    #
    @91
    @103
    cR
    wbr
    #
    wn
    #
    wi
    #
    @99
    va
    vt
    @103
    @14
    wceq
    #
    @108
    @96
    @110
    @98
    @112
    @105
    @93
    @107
    @95
    @112
    @104
    @73
    wph
    @92
    @103
    @14
    @9
    eleq1
    3anbi2d
    @112
    @106
    @77
    @94
    @103
    @14
    cF
    fveq2
    eqeq1d
    anbi12d
    @112
    @109
    @97
    @103
    @14
    @91
    cR
    breq2
    notbid
    imbi12d
    wph
    @104
    @73
    w3a
    #
    @106
    @77
    wceq
    #
    wa
    #
    @14
    @103
    cR
    wbr
    #
    wn
    #
    wi
    #
    @111
    vt
    vb
    @14
    @91
    wceq
    #
    @115
    @108
    @117
    @110
    @119
    @113
    @105
    @114
    @107
    @119
    @73
    @92
    wph
    @104
    @14
    @91
    @9
    eleq1
    3anbi3d
    @119
    @77
    @94
    @106
    @14
    @91
    cF
    fveq2
    eqeq2d
    anbi12d
    @119
    @116
    @109
    @14
    @91
    @103
    cR
    breq1
    notbid
    imbi12d
    @79
    @83
    wi
    @118
    vw
    va
    @63
    @103
    wceq
    #
    @79
    @115
    @83
    @117
    @120
    @75
    @113
    @78
    @114
    @120
    @72
    @104
    wph
    @73
    @63
    @103
    @9
    eleq1
    3anbi2d
    @120
    @76
    @106
    @77
    @63
    @103
    cF
    fveq2
    eqeq1d
    anbi12d
    @120
    @82
    @116
    @63
    @103
    @14
    cR
    breq2
    notbid
    imbi12d
    @79
    @87
    @83
    @89
    @79
    @86
    @83
    vu
    @1
    @75
    @78
    vu
    wph
    @72
    @73
    vu
    wph
    vu
    nfv
    vu
    @63
    @9
    vu
    @63
    nfcv
    vu
    cG
    vu
    cG
    @49
    @58
    vu
    @1
    @22
    nfmpt1
    nfcxfr
    nfrn
    #
    nfel
    vu
    vt
    @9
    @121
    nfcri
    nf3an
    @78
    vu
    nfv
    nfan
    @83
    vu
    nfv
    @79
    @24
    @86
    @83
    @79
    @24
    @86
    w3a
    #
    @83
    vt
    @20
    wral
    #
    @14
    @20
    wcel
    #
    @83
    @75
    @24
    @86
    @123
    @78
    @75
    @24
    @86
    w3a
    #
    @123
    @22
    @63
    wceq
    #
    @125
    @63
    @22
    @75
    @24
    @86
    simp3
    #
    eqcomd
    @125
    @63
    @20
    wcel
    #
    @32
    @123
    @126
    wb
    @125
    wph
    @24
    @86
    @128
    wph
    @72
    @73
    @24
    @86
    simp11
    #
    @75
    @24
    @86
    simp2
    #
    @127
    wph
    @24
    @86
    w3a
    #
    @128
    @123
    @131
    @128
    @123
    wa
    #
    @123
    vw
    @20
    crio
    #
    @63
    wceq
    #
    @86
    wph
    @134
    @24
    @86
    @63
    @22
    @133
    @86
    id
    @22
    @133
    wceq
    @86
    @21
    @123
    vv
    vw
    @20
    @0
    @63
    wceq
    #
    @16
    @83
    vt
    @20
    @135
    @15
    @82
    @0
    @63
    @14
    cR
    breq2
    notbid
    ralbidv
    #
    cbvriotav
    a1i
    eqtr2d
    3ad2ant3
    wph
    @24
    @132
    @134
    wb
    #
    @86
    @25
    @123
    vw
    @20
    wreu
    #
    @137
    @25
    @32
    @138
    @39
    @21
    @123
    vv
    vw
    @20
    @136
    cbvreuv
    sylib
    @123
    vw
    @20
    riota1
    syl
    3adant3
    mpbird
    simpld
    syl3anc
    #
    @125
    wph
    @24
    @32
    @129
    @130
    @39
    syl2anc
    @21
    @123
    vv
    @20
    @63
    @136
    riota2
    syl2anc
    mpbird
    3adant1r
    @122
    @124
    @14
    cA
    wcel
    #
    @77
    @18
    wceq
    #
    wa
    #
    @122
    @140
    @141
    @79
    @24
    @140
    @86
    @75
    @140
    @78
    wph
    @73
    @140
    @72
    wph
    @9
    cA
    @14
    @59
    sselda
    3adant2
    adantr
    #
    3ad2ant1
    @122
    @77
    @76
    @18
    @79
    @24
    @85
    @86
    @78
    @85
    @75
    @24
    @90
    ad2antlr
    3adant3
    @75
    @24
    @86
    @76
    @18
    wceq
    #
    @78
    @125
    @63
    cA
    wcel
    #
    @144
    @125
    @128
    @145
    @144
    wa
    #
    @139
    @125
    wph
    @29
    @128
    @146
    wb
    #
    @129
    wessf1ornlem.f
    cA
    @18
    @63
    cF
    fniniseg
    #
    3syl
    mpbid
    simprd
    3adant1r
    eqtrd
    jca
    @79
    @24
    @124
    @142
    wb
    #
    @86
    @75
    @149
    @78
    @24
    wph
    @72
    @149
    @73
    wph
    @29
    @149
    wessf1ornlem.f
    cA
    @18
    @14
    cF
    fniniseg
    syl
    3ad2ant1
    ad2antrr
    3adant3
    mpbird
    @83
    vt
    @20
    rspa
    syl2anc
    3exp
    rexlimd
    mpd
    #
    chvarv
    chvarv
    chvarv
    chvarv
    syl31anc
    @150
    jca
    @79
    cA
    cR
    wor
    #
    @145
    @140
    @67
    @84
    wb
    wph
    @72
    @78
    @151
    @73
    wph
    @151
    @78
    wph
    @33
    @151
    wessf1ornlem.r
    cA
    cR
    weso
    syl
    adantr
    3ad2antl1
    @75
    @145
    @78
    wph
    @72
    @145
    @73
    wph
    @9
    cA
    @63
    @59
    sselda
    3adant3
    adantr
    @143
    cA
    @63
    @14
    cR
    sotrieq2
    syl12anc
    mpbird
    syl2anc
    ex
    syl3anc
    ralrimivva
    jca
    vw
    vt
    @9
    @1
    @11
    dff13
    sylibr
    wph
    @62
    @18
    @64
    wceq
    #
    vw
    @9
    wrex
    #
    vu
    @1
    wral
    #
    wa
    @61
    wph
    @62
    @154
    @71
    wph
    @153
    vu
    @1
    @25
    @18
    cG
    cfv
    #
    @9
    wcel
    #
    @18
    @155
    @11
    cfv
    #
    wceq
    #
    @153
    wph
    @1
    @9
    @18
    cG
    wph
    cG
    @1
    wfn
    #
    @1
    @9
    cG
    wf
    #
    wph
    @22
    cvv
    wcel
    #
    vu
    @1
    wral
    #
    @159
    @162
    wph
    @161
    vu
    @1
    @21
    vv
    @20
    riotaex
    #
    rgenw
    a1i
    vu
    @1
    @22
    cG
    cvv
    @58
    fnmpt
    syl
    @159
    @160
    @1
    cG
    dffn3
    biimpi
    syl
    ffvelrnda
    #
    @25
    @157
    @155
    cF
    cfv
    #
    @18
    @25
    @156
    @157
    @165
    wceq
    @164
    @155
    @9
    cF
    fvres
    syl
    @25
    @155
    cA
    wcel
    #
    @165
    @18
    wceq
    #
    @25
    @155
    @20
    wcel
    #
    @166
    @167
    wa
    #
    @25
    @155
    @22
    @20
    @25
    @24
    @161
    @155
    @22
    wceq
    @25
    @36
    @24
    @38
    @37
    sylibr
    @161
    @25
    @163
    a1i
    vu
    @1
    @22
    cvv
    cG
    @58
    fvmpt2
    syl2anc
    @40
    eqeltrd
    wph
    @168
    @169
    wb
    #
    @24
    wph
    @147
    wi
    wph
    @170
    wi
    vw
    @155
    @18
    cG
    fvex
    @63
    @155
    wceq
    #
    @147
    @170
    wph
    @171
    @128
    @168
    @146
    @169
    @63
    @155
    @20
    eleq1
    @171
    @145
    @166
    @144
    @167
    @63
    @155
    cA
    eleq1
    @171
    @76
    @165
    @18
    @63
    @155
    cF
    fveq2
    eqeq1d
    anbi12d
    bibi12d
    imbi2d
    wph
    @29
    @147
    wessf1ornlem.f
    @148
    syl
    vtocl
    adantr
    mpbid
    simprd
    eqtr2d
    @152
    @158
    vw
    @155
    @9
    @171
    @64
    @157
    @18
    @63
    @155
    @11
    fveq2
    eqeq2d
    rspcev
    syl2anc
    ralrimiva
    jca
    vw
    vu
    @9
    @1
    @11
    dffo3
    sylibr
    jca
    @9
    @1
    @11
    df-f1o
    sylibr
    @3
    @12
    vv
    @9
    @4
    vv
    @9
    @1
    @11
    vv
    cF
    @9
    vv
    cF
    nfcv
    vv
    cG
    vv
    cG
    @49
    @58
    vv
    vu
    @1
    @22
    vv
    @1
    nfcv
    #
    @21
    vv
    @20
    nfriota1
    nfmpt
    nfcxfr
    nfrn
    #
    nfres
    @173
    @172
    nff1o
    @0
    @9
    wceq
    #
    @0
    @9
    @1
    @1
    @2
    @11
    @0
    @9
    cF
    reseq2
    @174
    id
    @174
    @1
    eqidd
    f1oeq123d
    rspce
    syl2anc
    @3
    @8
    vv
    vx
    @4
    @0
    @6
    wceq
    #
    @0
    @6
    @1
    @1
    @2
    @7
    @0
    @6
    cF
    reseq2
    @175
    id
    @175
    @1
    eqidd
    f1oeq123d
    cbvrexv
    sylib
end
