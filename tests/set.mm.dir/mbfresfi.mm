include "cc.mm"
include "wf.mm"
include "cv.mm"
include "cres.mm"
include "cmbf.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cuni.mm"
include "wceq.mm"
include "cvv.mm"
include "wi.mm"
include "cfn.mm"
include "uniexg.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "fex.mm"
include "ex.mm"
include "jcai.mm"
include "feq2.mm"
include "anbi1d.mm"
include "eqeq2.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "imbi2d.mm"
include "feq1.mm"
include "reseq1.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "wal.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "rzal.mm"
include "biantrud.mm"
include "bicomd.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "eqeq1d.mm"
include "2albidv.mm"
include "weq.mm"
include "raleq.mm"
include "anbi2d.mm"
include "simpl.mm"
include "simpr.mm"
include "feq12d.mm"
include "adantr.mm"
include "wb.mm"
include "adantl.mm"
include "cbval2v.mm"
include "syl6bb.mm"
include "wrel.mm"
include "cdm.mm"
include "frel.mm"
include "fdm.mm"
include "eqcom.mm"
include "biimpi.mm"
include "sylan9eq.mm"
include "reldm0.mm"
include "biimpar.mm"
include "0mbf.mm"
include "syl6eqel.mm"
include "syl2anc.mm"
include "gen2.mm"
include "cre.mm"
include "ccom.mm"
include "cim.mm"
include "cr.mm"
include "ref.mm"
include "fco.mm"
include "mpan.mm"
include "ad2antrl.mm"
include "ccncf.mm"
include "co.mm"
include "recncf.mm"
include "elexi.mm"
include "vex.mm"
include "coex.mm"
include "resex.mm"
include "vuniex.mm"
include "eqid.mm"
include "feq123.mm"
include "mp3an3.mm"
include "bitr3d.mm"
include "spc2gv.mm"
include "mp2an.mm"
include "wss.mm"
include "ax-resscn.mm"
include "fss.mm"
include "ssun1.mm"
include "unissi.mm"
include "id.mm"
include "syl5sseq.mm"
include "fssres.mm"
include "syl2an.mm"
include "adantlr.mm"
include "wel.mm"
include "elssuni.mm"
include "resabs1d.mm"
include "resco.mm"
include "elun1.mm"
include "reseq2.mm"
include "rspccva.mm"
include "sylan2.mm"
include "adantll.mm"
include "cin.mm"
include "fresin.mm"
include "ismbfcn.mm"
include "biimpd.mm"
include "ad2antrr.mm"
include "mpd.mm"
include "simpld.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "cbvralv.mm"
include "sylib.mm"
include "pm2.27.mm"
include "mpan9.mm"
include "vsnid.mm"
include "elun2.mm"
include "rspcv.mm"
include "mp2b.mm"
include "simprbda.mm"
include "syl5eqel.mm"
include "uniun.mm"
include "unisn.mm"
include "uneq2i.mm"
include "eqtri.mm"
include "syl5eqr.mm"
include "ad2antll.mm"
include "mbfres2.mm"
include "imf.mm"
include "imcncf.mm"
include "simprd.mm"
include "simplbda.mm"
include "mpbir2and.mm"
include "alrimivv.mm"
include "a1i.mm"
include "findcard2.mm"
include "2sp.mm"
include "3syl.mm"
include "vtocl2g.mm"
include "mpcom.mm"
include "mpan2d.mm"
include "mp2and.mm"

theorem mbfresfi
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cF: class F
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vr: setvar r
  let vt: setvar t
  assume mbfresfi.1: |- ( ph -> F : A --> CC )
  assume mbfresfi.2: |- ( ph -> S e. Fin )
  assume mbfresfi.3: |- ( ph -> A. s e. S ( F |` s ) e. MblFn )
  assume mbfresfi.4: |- ( ph -> U. S = A )

  disjoint ph s
  disjoint A s
  disjoint F s
  disjoint S s
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a ph
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b ph
  disjoint f g
  disjoint f h
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f ph
  disjoint g h
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g ph
  disjoint h r
  disjoint h s
  disjoint h t
  disjoint h ph
  disjoint r s
  disjoint r t
  disjoint ph r
  disjoint s t
  disjoint ph t
  disjoint A a
  disjoint A b
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A r
  disjoint A t
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F r
  disjoint F t
  disjoint S a
  disjoint S b
  disjoint S f
  disjoint S g
  disjoint S h
  disjoint S r
  disjoint S t
  assert |- ( ph -> F e. MblFn )

  proof
    wph
    cA
    cc
    cF
    wf
    #
    cF
    vs
    cv
    #
    cres
    #
    cmbf
    wcel
    #
    vs
    cS
    wral
    #
    cF
    cmbf
    wcel
    #
    mbfresfi.1
    mbfresfi.3
    wph
    @0
    @4
    wa
    #
    cS
    cuni
    #
    cA
    wceq
    #
    @5
    mbfresfi.4
    cA
    cvv
    wcel
    #
    cF
    cvv
    wcel
    #
    wa
    wph
    @6
    @8
    wa
    #
    @5
    wi
    #
    wph
    @9
    @10
    wph
    @7
    cA
    cvv
    mbfresfi.4
    wph
    cS
    cfn
    wcel
    #
    @7
    cvv
    wcel
    mbfresfi.2
    cS
    cfn
    uniexg
    syl
    eqeltrrd
    wph
    @0
    @9
    @10
    wi
    mbfresfi.1
    @0
    @9
    @10
    cA
    cc
    cvv
    cF
    fex
    ex
    syl
    jcai
    wph
    va
    cv
    #
    cc
    vf
    cv
    #
    wf
    #
    @15
    @1
    cres
    #
    cmbf
    wcel
    #
    vs
    cS
    wral
    #
    wa
    #
    @7
    @14
    wceq
    #
    wa
    #
    @15
    cmbf
    wcel
    #
    wi
    #
    wi
    wph
    cA
    cc
    @15
    wf
    #
    @19
    wa
    #
    @8
    wa
    #
    @23
    wi
    #
    wi
    wph
    @12
    wi
    va
    vf
    cA
    cF
    cvv
    cvv
    @14
    cA
    wceq
    #
    @24
    @28
    wph
    @29
    @22
    @27
    @23
    @29
    @20
    @26
    @21
    @8
    @29
    @16
    @25
    @19
    @14
    cA
    cc
    @15
    feq2
    anbi1d
    @14
    cA
    @7
    eqeq2
    anbi12d
    imbi1d
    imbi2d
    @15
    cF
    wceq
    #
    @28
    @12
    wph
    @30
    @27
    @11
    @23
    @5
    @30
    @26
    @6
    @8
    @30
    @25
    @0
    @19
    @4
    cA
    cc
    @15
    cF
    feq1
    @30
    @18
    @3
    vs
    cS
    @30
    @17
    @2
    cmbf
    @15
    cF
    @1
    reseq1
    eleq1d
    ralbidv
    anbi12d
    anbi1d
    @15
    cF
    cmbf
    eleq1
    imbi12d
    imbi2d
    wph
    @13
    @24
    va
    wal
    vf
    wal
    #
    @24
    mbfresfi.2
    @16
    @18
    vs
    vr
    cv
    #
    wral
    #
    wa
    #
    @32
    cuni
    #
    @14
    wceq
    #
    wa
    #
    @23
    wi
    #
    va
    wal
    vf
    wal
    #
    @16
    c0
    @14
    wceq
    #
    wa
    #
    @23
    wi
    #
    va
    wal
    vf
    wal
    vb
    cv
    #
    cc
    vg
    cv
    #
    wf
    #
    @44
    @1
    cres
    #
    cmbf
    wcel
    #
    vs
    vt
    cv
    #
    wral
    #
    wa
    #
    @48
    cuni
    #
    @43
    wceq
    #
    wa
    #
    @44
    cmbf
    wcel
    #
    wi
    #
    vb
    wal
    vg
    wal
    #
    @16
    @18
    vs
    @48
    vh
    cv
    #
    csn
    #
    cun
    #
    wral
    #
    wa
    #
    @59
    cuni
    #
    @14
    wceq
    #
    wa
    #
    @23
    wi
    #
    va
    wal
    vf
    wal
    #
    @31
    vr
    vt
    vh
    cS
    @32
    c0
    wceq
    #
    @38
    @42
    vf
    va
    @67
    @37
    @41
    @23
    @67
    @34
    @16
    @36
    @40
    @67
    @16
    @34
    @67
    @33
    @16
    @18
    vs
    @32
    rzal
    biantrud
    bicomd
    @67
    @35
    c0
    @14
    @67
    @35
    c0
    cuni
    c0
    @32
    c0
    unieq
    uni0
    syl6eq
    eqeq1d
    anbi12d
    imbi1d
    2albidv
    vr
    vt
    weq
    #
    @39
    @16
    @18
    vs
    @48
    wral
    #
    wa
    #
    @51
    @14
    wceq
    #
    wa
    #
    @23
    wi
    #
    va
    wal
    vf
    wal
    @56
    @68
    @38
    @73
    vf
    va
    @68
    @37
    @72
    @23
    @68
    @34
    @70
    @36
    @71
    @68
    @33
    @69
    @16
    @18
    vs
    @32
    @48
    raleq
    anbi2d
    @68
    @35
    @51
    @14
    @32
    @48
    unieq
    eqeq1d
    anbi12d
    imbi1d
    2albidv
    @73
    @55
    vf
    va
    vg
    vb
    vf
    vg
    weq
    #
    va
    vb
    weq
    #
    wa
    #
    @72
    @53
    @23
    @54
    @76
    @70
    @50
    @71
    @52
    @76
    @16
    @45
    @69
    @49
    @76
    @14
    @43
    cc
    @15
    @44
    @74
    @75
    simpl
    @74
    @75
    simpr
    feq12d
    @76
    @18
    @47
    vs
    @48
    @76
    @17
    @46
    cmbf
    @74
    @17
    @46
    wceq
    @75
    @15
    @44
    @1
    reseq1
    adantr
    eleq1d
    ralbidv
    anbi12d
    @75
    @71
    @52
    wb
    @74
    @14
    @43
    @51
    eqeq2
    adantl
    anbi12d
    @74
    @23
    @54
    wb
    @75
    @15
    @44
    cmbf
    eleq1
    adantr
    imbi12d
    cbval2v
    syl6bb
    @32
    @59
    wceq
    #
    @38
    @65
    vf
    va
    @77
    @37
    @64
    @23
    @77
    @34
    @61
    @36
    @63
    @77
    @33
    @60
    @16
    @18
    vs
    @32
    @59
    raleq
    anbi2d
    @77
    @35
    @62
    @14
    @32
    @59
    unieq
    eqeq1d
    anbi12d
    imbi1d
    2albidv
    @32
    cS
    wceq
    #
    @38
    @24
    vf
    va
    @78
    @37
    @22
    @23
    @78
    @34
    @20
    @36
    @21
    @78
    @33
    @19
    @16
    @18
    vs
    @32
    cS
    raleq
    anbi2d
    @78
    @35
    @7
    @14
    @32
    cS
    unieq
    eqeq1d
    anbi12d
    imbi1d
    2albidv
    @42
    vf
    va
    @41
    @15
    wrel
    #
    @15
    cdm
    #
    c0
    wceq
    #
    @23
    @16
    @79
    @40
    @14
    cc
    @15
    frel
    adantr
    @16
    @40
    @80
    @14
    c0
    @14
    cc
    @15
    fdm
    @40
    @14
    c0
    wceq
    c0
    @14
    eqcom
    biimpi
    sylan9eq
    @79
    @81
    wa
    @15
    c0
    cmbf
    @79
    @15
    c0
    wceq
    @81
    @15
    reldm0
    biimpar
    0mbf
    syl6eqel
    syl2anc
    gen2
    @56
    @66
    wi
    @48
    cfn
    wcel
    @56
    @65
    vf
    va
    @56
    @64
    @23
    @56
    @64
    wa
    #
    @23
    cre
    @15
    ccom
    #
    cmbf
    wcel
    #
    cim
    @15
    ccom
    #
    cmbf
    wcel
    #
    @82
    @14
    @51
    @57
    @83
    @61
    @14
    cr
    @83
    wf
    #
    @56
    @63
    @16
    @87
    @60
    cc
    cr
    cre
    wf
    #
    @16
    @87
    ref
    @14
    cc
    cr
    cre
    @15
    fco
    mpan
    adantr
    ad2antrl
    @56
    @51
    cc
    @83
    @51
    cres
    #
    wf
    #
    @89
    @1
    cres
    #
    cmbf
    wcel
    #
    vs
    @48
    wral
    #
    wa
    #
    @89
    cmbf
    wcel
    #
    wi
    #
    @64
    @95
    @89
    cvv
    wcel
    @51
    cvv
    wcel
    #
    @56
    @96
    wi
    @83
    @51
    cre
    @15
    cre
    cc
    cr
    ccncf
    co
    #
    recncf
    elexi
    vf
    vex
    #
    coex
    resex
    vt
    vuniex
    #
    @55
    @96
    vg
    vb
    @89
    @51
    cvv
    cvv
    @44
    @89
    wceq
    #
    @43
    @51
    wceq
    #
    wa
    #
    @53
    @94
    @54
    @95
    @103
    @50
    @53
    @94
    @103
    @52
    @50
    @102
    @52
    @101
    @102
    @52
    @43
    @51
    eqcom
    biimpi
    #
    adantl
    biantrud
    @103
    @45
    @90
    @49
    @93
    @101
    @102
    cc
    cc
    wceq
    #
    @45
    @90
    wb
    cc
    eqid
    #
    @43
    cc
    @51
    cc
    @44
    @89
    feq123
    mp3an3
    @103
    @47
    @92
    vs
    @48
    @101
    @47
    @92
    wb
    @102
    @101
    @46
    @91
    cmbf
    @44
    @89
    @1
    reseq1
    eleq1d
    adantr
    ralbidv
    anbi12d
    bitr3d
    @101
    @54
    @95
    wb
    @102
    @44
    @89
    cmbf
    eleq1
    adantr
    imbi12d
    spc2gv
    mp2an
    @64
    @90
    @93
    @96
    @95
    wi
    @16
    @63
    @90
    @60
    @16
    @14
    cc
    @83
    wf
    #
    @51
    @14
    wss
    #
    @90
    @63
    cc
    cc
    cre
    wf
    #
    @16
    @107
    @88
    cr
    cc
    wss
    #
    @109
    ref
    ax-resscn
    cc
    cr
    cc
    cre
    fss
    mp2an
    @14
    cc
    cc
    cre
    @15
    fco
    mpan
    @63
    @62
    @51
    @14
    @48
    @59
    @48
    @58
    ssun1
    unissi
    @63
    id
    #
    syl5sseq
    #
    @14
    cc
    @51
    @83
    fssres
    syl2an
    adantlr
    @61
    @93
    @63
    @61
    @89
    @32
    cres
    #
    cmbf
    wcel
    #
    vr
    @48
    wral
    @93
    @61
    @114
    vr
    @48
    @61
    vr
    vt
    wel
    #
    wa
    #
    @113
    cre
    @15
    @32
    cres
    #
    ccom
    #
    cmbf
    @115
    @113
    @118
    wceq
    @61
    @115
    @113
    @83
    @32
    cres
    @118
    @115
    @83
    @32
    @51
    @32
    @48
    elssuni
    #
    resabs1d
    cre
    @15
    @32
    resco
    syl6eq
    adantl
    @116
    @118
    cmbf
    wcel
    #
    cim
    @117
    ccom
    #
    cmbf
    wcel
    #
    @116
    @117
    cmbf
    wcel
    #
    @120
    @122
    wa
    #
    @60
    @115
    @123
    @16
    @115
    @60
    @32
    @59
    wcel
    @123
    @32
    @48
    @58
    elun1
    @18
    @123
    vs
    @32
    @59
    vs
    vr
    weq
    @17
    @117
    cmbf
    @1
    @32
    @15
    reseq2
    eleq1d
    rspccva
    sylan2
    adantll
    @16
    @123
    @124
    wi
    @60
    @115
    @16
    @123
    @124
    @16
    @14
    @32
    cin
    #
    cc
    @117
    wf
    @123
    @124
    wb
    @14
    cc
    @15
    @32
    fresin
    @125
    @117
    ismbfcn
    syl
    biimpd
    ad2antrr
    mpd
    #
    simpld
    eqeltrd
    ralrimiva
    @114
    @92
    vr
    vs
    @48
    vr
    vs
    weq
    #
    @113
    @91
    cmbf
    @32
    @1
    @89
    reseq2
    eleq1d
    cbvralv
    sylib
    adantr
    @94
    @95
    pm2.27
    syl2anc
    mpan9
    @61
    @83
    @57
    cres
    #
    cmbf
    wcel
    #
    @56
    @63
    @60
    @16
    @15
    @57
    cres
    #
    cmbf
    wcel
    #
    @129
    @57
    @58
    wcel
    @57
    @59
    wcel
    @60
    @131
    wi
    vh
    vsnid
    @57
    @58
    @48
    elun2
    @18
    @131
    vs
    @57
    @59
    vs
    vh
    weq
    @17
    @130
    cmbf
    @1
    @57
    @15
    reseq2
    eleq1d
    rspcv
    mp2b
    #
    @16
    @131
    wa
    #
    @128
    cre
    @130
    ccom
    #
    cmbf
    cre
    @15
    @57
    resco
    @16
    @131
    @134
    cmbf
    wcel
    #
    cim
    @130
    ccom
    #
    cmbf
    wcel
    #
    @16
    @14
    @57
    cin
    #
    cc
    @130
    wf
    @131
    @135
    @137
    wa
    wb
    @14
    cc
    @15
    @57
    fresin
    @138
    @130
    ismbfcn
    syl
    #
    simprbda
    syl5eqel
    sylan2
    ad2antrl
    @63
    @51
    @57
    cun
    #
    @14
    wceq
    @56
    @61
    @63
    @140
    @62
    @14
    @62
    @51
    @58
    cuni
    #
    cun
    @140
    @48
    @58
    uniun
    @141
    @57
    @51
    @57
    vh
    vex
    unisn
    uneq2i
    eqtri
    @111
    syl5eqr
    ad2antll
    #
    mbfres2
    @82
    @14
    @51
    @57
    @85
    @61
    @14
    cr
    @85
    wf
    #
    @56
    @63
    @16
    @143
    @60
    cc
    cr
    cim
    wf
    #
    @16
    @143
    imf
    @14
    cc
    cr
    cim
    @15
    fco
    mpan
    adantr
    ad2antrl
    @56
    @51
    cc
    @85
    @51
    cres
    #
    wf
    #
    @145
    @1
    cres
    #
    cmbf
    wcel
    #
    vs
    @48
    wral
    #
    wa
    #
    @145
    cmbf
    wcel
    #
    wi
    #
    @64
    @151
    @145
    cvv
    wcel
    @97
    @56
    @152
    wi
    @85
    @51
    cim
    @15
    cim
    @98
    imcncf
    elexi
    @99
    coex
    resex
    @100
    @55
    @152
    vg
    vb
    @145
    @51
    cvv
    cvv
    @44
    @145
    wceq
    #
    @102
    wa
    #
    @53
    @150
    @54
    @151
    @154
    @50
    @53
    @150
    @154
    @52
    @50
    @102
    @52
    @153
    @104
    adantl
    biantrud
    @154
    @45
    @146
    @49
    @149
    @153
    @102
    @105
    @45
    @146
    wb
    @106
    @43
    cc
    @51
    cc
    @44
    @145
    feq123
    mp3an3
    @154
    @47
    @148
    vs
    @48
    @153
    @47
    @148
    wb
    @102
    @153
    @46
    @147
    cmbf
    @44
    @145
    @1
    reseq1
    eleq1d
    adantr
    ralbidv
    anbi12d
    bitr3d
    @153
    @54
    @151
    wb
    @102
    @44
    @145
    cmbf
    eleq1
    adantr
    imbi12d
    spc2gv
    mp2an
    @64
    @146
    @149
    @152
    @151
    wi
    @16
    @63
    @146
    @60
    @16
    @14
    cc
    @85
    wf
    #
    @108
    @146
    @63
    cc
    cc
    cim
    wf
    #
    @16
    @155
    @144
    @110
    @156
    imf
    ax-resscn
    cc
    cr
    cc
    cim
    fss
    mp2an
    @14
    cc
    cc
    cim
    @15
    fco
    mpan
    @112
    @14
    cc
    @51
    @85
    fssres
    syl2an
    adantlr
    @61
    @149
    @63
    @61
    @145
    @32
    cres
    #
    cmbf
    wcel
    #
    vr
    @48
    wral
    @149
    @61
    @158
    vr
    @48
    @116
    @157
    @121
    cmbf
    @115
    @157
    @121
    wceq
    @61
    @115
    @157
    @85
    @32
    cres
    @121
    @115
    @85
    @32
    @51
    @119
    resabs1d
    cim
    @15
    @32
    resco
    syl6eq
    adantl
    @116
    @120
    @122
    @126
    simprd
    eqeltrd
    ralrimiva
    @158
    @148
    vr
    vs
    @48
    @127
    @157
    @147
    cmbf
    @32
    @1
    @145
    reseq2
    eleq1d
    cbvralv
    sylib
    adantr
    @150
    @151
    pm2.27
    syl2anc
    mpan9
    @61
    @85
    @57
    cres
    #
    cmbf
    wcel
    #
    @56
    @63
    @60
    @16
    @131
    @160
    @132
    @133
    @159
    @136
    cmbf
    cim
    @15
    @57
    resco
    @16
    @131
    @135
    @137
    @139
    simplbda
    syl5eqel
    sylan2
    ad2antrl
    @142
    mbfres2
    @61
    @23
    @84
    @86
    wa
    wb
    #
    @56
    @63
    @16
    @161
    @60
    @14
    @15
    ismbfcn
    adantr
    ad2antrl
    mpbir2and
    ex
    alrimivv
    a1i
    findcard2
    @24
    vf
    va
    2sp
    3syl
    vtocl2g
    mpcom
    mpan2d
    mp2and
end
