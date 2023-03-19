include "wcel.mm"
include "cfi.mm"
include "cfv.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "crn.mm"
include "cuni.mm"
include "cima.mm"
include "cv.mm"
include "wss.mm"
include "cin.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "dffi2.mm"
include "c0.mm"
include "fr0g.mm"
include "wfn.mm"
include "frfnom.mm"
include "peano1.mm"
include "fnfvelrn.mm"
include "mp2an.mm"
include "syl6eqelr.mm"
include "elssuni.mm"
include "syl.mm"
include "wrex.mm"
include "ciun.mm"
include "reeanv.mm"
include "eliun.mm"
include "anbi12i.mm"
include "wb.mm"
include "fniunfv.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "ax-mp.mm"
include "3bitr2i.mm"
include "cun.mm"
include "wi.mm"
include "word.mm"
include "ordom.mm"
include "ordunel.mm"
include "mp3an1.mm"
include "adantl.mm"
include "simprl.mm"
include "jca.mm"
include "weq.mm"
include "wo.mm"
include "con0.mm"
include "nnon.mm"
include "ad2antlr.mm"
include "onsseleq.mm"
include "syl2anc.mm"
include "csuc.mm"
include "wceq.mm"
include "rzal.mm"
include "biantrud.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "bitr3d.mm"
include "sseq2d.mm"
include "raleqbi1dv.mm"
include "ssfii.mm"
include "eqsstrd.mm"
include "csn.mm"
include "cmpt2.mm"
include "id.mm"
include "eqidd.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "ineq2.mm"
include "inidm.mm"
include "syl6eq.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "eqid.mm"
include "rnmpt2.mm"
include "abeq2i.mm"
include "sylibr.mm"
include "ssriv.mm"
include "cvv.mm"
include "simpl.mm"
include "cpw.mm"
include "fvex.mm"
include "uniex.mm"
include "pwex.mm"
include "cxp.mm"
include "wf.mm"
include "inss1.mm"
include "adantr.mm"
include "syl5ss.mm"
include "vex.mm"
include "inex1.mm"
include "elpw.mm"
include "rgen2a.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "frn.mm"
include "ssexi.mm"
include "nfcv.mm"
include "cmpt.mm"
include "mpt2eq12.mm"
include "anidms.mm"
include "cbvmpt2v.mm"
include "rneqd.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "rdgeq1.mm"
include "reseq1i.mm"
include "frsucmpt.mm"
include "sylancl.mm"
include "syl5sseqr.mm"
include "sstr2.mm"
include "syl5com.mm"
include "ralimdv.mm"
include "ralsn.mm"
include "jctird.mm"
include "df-suc.mm"
include "raleqi.mm"
include "ralunb.mm"
include "bitri.mm"
include "syl6ibr.mm"
include "fiin.mm"
include "ssralv.mm"
include "syld.mm"
include "mpi.mm"
include "sylib.mm"
include "jctild.mm"
include "expimpd.mm"
include "a1d.mm"
include "finds2.mm"
include "impcom.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "ex.mm"
include "eqimss.mm"
include "a1i.mm"
include "jaod.mm"
include "sylbid.mm"
include "ralrimiva.mm"
include "ssun1.mm"
include "sseq2.mm"
include "imbi12d.mm"
include "sseq1.mm"
include "rspc2v.mm"
include "syl3c.mm"
include "sseld.mm"
include "simprr.mm"
include "ssun2.mm"
include "peano2.mm"
include "ssiun2s.mm"
include "3syl.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "elab.mm"
include "syl6eleqr.mm"
include "eleqtrrd.mm"
include "sseldd.mm"
include "syl6eleq.mm"
include "syl2and.mm"
include "rexlimdvva.mm"
include "imp.mm"
include "sylan2br.mm"
include "ralrimivva.mm"
include "simpld.mm"
include "elpw2.mm"
include "fnfvrnss.mm"
include "sylancr.mm"
include "sspwuni.mm"
include "ssexg.mm"
include "eleq2.mm"
include "elabg.mm"
include "mpbir2and.mm"
include "intss1.mm"
include "eqssd.mm"
include "df-ima.mm"
include "unieqi.mm"
include "syl6eqr.mm"

theorem dffi3
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cA: class A
  let cR: class R
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vm: setvar m
  let vn: setvar n
  let vv: setvar v
  let vx: setvar x
  assume dffi3.1: |- R = ( u e. _V |-> ran ( y e. u , z e. u |-> ( y i^i z ) ) )

  disjoint A y
  disjoint R y
  disjoint V y
  disjoint u y
  disjoint u z
  disjoint y z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a m
  disjoint a n
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint b m
  disjoint b n
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint c d
  disjoint c m
  disjoint c n
  disjoint c v
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint d m
  disjoint d n
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint A d
  disjoint m n
  disjoint m v
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint v x
  disjoint v y
  disjoint A v
  disjoint x y
  disjoint A x
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint R m
  disjoint R n
  disjoint R v
  disjoint R x
  disjoint V c
  disjoint V d
  disjoint V m
  disjoint V n
  disjoint V x
  disjoint a u
  disjoint a z
  disjoint b u
  disjoint b z
  disjoint u v
  disjoint v z
  assert |- ( A e. V -> ( fi ` A ) = U. ( rec ( R , A ) " _om ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cfi
    cfv
    #
    cR
    cA
    crdg
    #
    com
    cres
    #
    crn
    #
    cuni
    #
    @2
    com
    cima
    #
    cuni
    @0
    @1
    @5
    @0
    @1
    cA
    vx
    cv
    #
    wss
    #
    vc
    cv
    #
    vd
    cv
    #
    cin
    #
    @7
    wcel
    #
    vd
    @7
    wral
    #
    vc
    @7
    wral
    #
    wa
    #
    vx
    cab
    #
    cint
    #
    @5
    vc
    vd
    vx
    cA
    cV
    dffi2
    @0
    @5
    @16
    wcel
    #
    @17
    @5
    wss
    @0
    @18
    cA
    @5
    wss
    #
    @11
    @5
    wcel
    #
    vd
    @5
    wral
    #
    vc
    @5
    wral
    #
    @0
    cA
    @4
    wcel
    @19
    @0
    cA
    c0
    @3
    cfv
    #
    @4
    cA
    cV
    cR
    fr0g
    #
    @3
    com
    wfn
    #
    c0
    com
    wcel
    @23
    @4
    wcel
    cA
    cR
    frfnom
    #
    peano1
    com
    c0
    @3
    fnfvelrn
    mp2an
    syl6eqelr
    cA
    @4
    elssuni
    syl
    @0
    @20
    vc
    vd
    @5
    @5
    @9
    @5
    wcel
    #
    @10
    @5
    wcel
    #
    wa
    #
    @0
    @9
    vm
    cv
    #
    @3
    cfv
    #
    wcel
    #
    @10
    vn
    cv
    #
    @3
    cfv
    #
    wcel
    #
    wa
    #
    vn
    com
    wrex
    vm
    com
    wrex
    #
    @20
    @37
    @32
    vm
    com
    wrex
    #
    @35
    vn
    com
    wrex
    #
    wa
    @9
    vm
    com
    @31
    ciun
    #
    wcel
    #
    @10
    vn
    com
    @34
    ciun
    #
    wcel
    #
    wa
    #
    @29
    @32
    @35
    vm
    vn
    com
    com
    reeanv
    @41
    @38
    @43
    @39
    vm
    @9
    com
    @31
    eliun
    vn
    @10
    com
    @34
    eliun
    anbi12i
    @25
    @44
    @29
    wb
    @26
    @25
    @41
    @27
    @43
    @28
    @25
    @40
    @5
    @9
    vm
    com
    @3
    fniunfv
    eleq2d
    @25
    @42
    @5
    @10
    vn
    com
    @3
    fniunfv
    eleq2d
    anbi12d
    ax-mp
    3bitr2i
    @0
    @37
    @20
    @0
    @36
    @20
    vm
    vn
    com
    com
    @0
    @30
    com
    wcel
    #
    @33
    com
    wcel
    #
    wa
    #
    wa
    #
    @32
    @9
    @30
    @33
    cun
    #
    @3
    cfv
    #
    wcel
    #
    @35
    @10
    @50
    wcel
    #
    @20
    @48
    @31
    @50
    @9
    @48
    @49
    com
    wcel
    #
    @45
    wa
    vy
    cv
    #
    @7
    wss
    #
    @54
    @3
    cfv
    #
    @7
    @3
    cfv
    #
    wss
    #
    wi
    #
    vy
    com
    wral
    #
    vx
    com
    wral
    #
    @30
    @49
    wss
    #
    @31
    @50
    wss
    #
    @48
    @53
    @45
    @47
    @53
    @0
    com
    word
    @45
    @46
    @53
    ordom
    com
    @30
    @33
    ordunel
    mp3an1
    #
    adantl
    #
    @0
    @45
    @46
    simprl
    jca
    @0
    @61
    @47
    @0
    @60
    vx
    com
    @0
    @7
    com
    wcel
    #
    wa
    #
    @59
    vy
    com
    @67
    @54
    com
    wcel
    #
    wa
    #
    @55
    @54
    @7
    wcel
    #
    vy
    vx
    weq
    #
    wo
    #
    @58
    @69
    @54
    con0
    wcel
    #
    @7
    con0
    wcel
    #
    @55
    @72
    wb
    @68
    @73
    @67
    @54
    nnon
    adantl
    @66
    @74
    @0
    @68
    @7
    nnon
    ad2antlr
    @54
    @7
    onsseleq
    syl2anc
    @69
    @70
    @58
    @71
    @67
    @70
    @58
    wi
    @68
    @67
    @70
    @58
    @67
    @58
    vy
    @7
    @67
    @57
    @1
    wss
    #
    @58
    vy
    @7
    wral
    #
    @66
    @0
    @75
    @76
    wa
    #
    @77
    @23
    @1
    wss
    #
    @34
    @1
    wss
    #
    @56
    @34
    wss
    #
    vy
    @33
    wral
    #
    wa
    #
    @33
    csuc
    #
    @3
    cfv
    #
    @1
    wss
    #
    @56
    @84
    wss
    #
    vy
    @83
    wral
    #
    wa
    #
    @0
    vx
    vn
    @7
    c0
    wceq
    #
    @75
    @77
    @78
    @89
    @76
    @75
    @58
    vy
    @7
    rzal
    biantrud
    @89
    @57
    @23
    @1
    @7
    c0
    @3
    fveq2
    sseq1d
    bitr3d
    vx
    vn
    weq
    #
    @75
    @79
    @76
    @81
    @90
    @57
    @34
    @1
    @7
    @33
    @3
    fveq2
    #
    sseq1d
    @58
    @80
    vy
    @7
    @33
    @90
    @57
    @34
    @56
    @91
    sseq2d
    raleqbi1dv
    anbi12d
    @7
    @83
    wceq
    #
    @75
    @85
    @76
    @87
    @92
    @57
    @84
    @1
    @7
    @83
    @3
    fveq2
    #
    sseq1d
    @58
    @86
    vy
    @7
    @83
    @92
    @57
    @84
    @56
    @93
    sseq2d
    raleqbi1dv
    anbi12d
    @0
    @23
    cA
    @1
    @24
    cA
    cV
    ssfii
    eqsstrd
    @46
    @82
    @88
    wi
    @0
    @46
    @79
    @81
    @88
    @46
    @79
    wa
    #
    @81
    @87
    @85
    @94
    @81
    @86
    vy
    @33
    wral
    #
    @86
    vy
    @33
    csn
    #
    wral
    #
    wa
    #
    @87
    @94
    @81
    @95
    @97
    @94
    @80
    @86
    vy
    @33
    @94
    @34
    @84
    wss
    #
    @80
    @86
    @94
    va
    vb
    @34
    @34
    va
    cv
    #
    vb
    cv
    #
    cin
    #
    cmpt2
    #
    crn
    #
    @34
    @84
    vx
    @34
    @104
    @7
    @34
    wcel
    #
    @7
    @102
    wceq
    #
    vb
    @34
    wrex
    va
    @34
    wrex
    #
    @7
    @104
    wcel
    @105
    @105
    @105
    vx
    vx
    weq
    #
    @107
    @105
    id
    #
    @109
    @105
    @7
    eqidd
    @106
    @108
    @7
    @7
    @101
    cin
    #
    wceq
    va
    vb
    @7
    @7
    @34
    @34
    va
    vx
    weq
    @102
    @110
    @7
    @100
    @7
    @101
    ineq1
    eqeq2d
    vb
    vx
    weq
    #
    @110
    @7
    @7
    @111
    @110
    @7
    @7
    cin
    @7
    @101
    @7
    @7
    ineq2
    @7
    inidm
    syl6eq
    eqeq2d
    rspc2ev
    syl3anc
    @107
    vx
    @104
    va
    vb
    vx
    @34
    @34
    @102
    @103
    @103
    eqid
    #
    rnmpt2
    abeq2i
    sylibr
    ssriv
    @94
    @46
    @104
    cvv
    wcel
    @84
    @104
    wceq
    @46
    @79
    simpl
    @104
    @34
    cuni
    #
    cpw
    #
    @113
    @34
    @33
    @3
    fvex
    uniex
    pwex
    @34
    @34
    cxp
    #
    @114
    @103
    wf
    #
    @104
    @114
    wss
    @102
    @114
    wcel
    #
    vb
    @34
    wral
    va
    @34
    wral
    @116
    @117
    va
    vb
    @34
    @100
    @34
    wcel
    #
    @101
    @34
    wcel
    #
    wa
    #
    @102
    @113
    wss
    @117
    @120
    @102
    @100
    @113
    @100
    @101
    inss1
    #
    @118
    @100
    @113
    wss
    @119
    @100
    @34
    elssuni
    adantr
    syl5ss
    @102
    @113
    @100
    @101
    va
    vex
    inex1
    #
    elpw
    sylibr
    rgen2a
    va
    vb
    @34
    @34
    @102
    @114
    @103
    @112
    fmpt2
    mpbi
    @115
    @114
    @103
    frn
    ax-mp
    ssexi
    vv
    cA
    @33
    va
    vb
    vv
    cv
    #
    @123
    @102
    cmpt2
    #
    crn
    #
    @104
    @3
    cvv
    vv
    cA
    nfcv
    #
    vv
    @33
    nfcv
    vv
    @104
    nfcv
    @2
    vv
    cvv
    @125
    cmpt
    #
    cA
    crdg
    #
    com
    cR
    @127
    wceq
    @2
    @128
    wceq
    cR
    vu
    cvv
    vy
    vz
    vu
    cv
    #
    @129
    @54
    vz
    cv
    #
    cin
    #
    cmpt2
    #
    crn
    #
    cmpt
    @127
    dffi3.1
    vu
    vv
    cvv
    @133
    @125
    vu
    vv
    weq
    #
    @132
    @124
    @134
    @132
    vy
    vz
    @123
    @123
    @131
    cmpt2
    #
    @124
    @134
    @132
    @135
    wceq
    vy
    vz
    @129
    @129
    @123
    @123
    @131
    mpt2eq12
    anidms
    vy
    vz
    va
    vb
    @123
    @123
    @131
    @102
    @100
    @130
    cin
    @54
    @100
    @130
    ineq1
    @130
    @101
    @100
    ineq2
    cbvmpt2v
    syl6eq
    rneqd
    cbvmptv
    eqtri
    cA
    cR
    @127
    rdgeq1
    ax-mp
    reseq1i
    #
    @123
    @34
    wceq
    #
    @124
    @103
    @137
    @124
    @103
    wceq
    va
    vb
    @123
    @123
    @34
    @34
    @102
    mpt2eq12
    anidms
    rneqd
    frsucmpt
    sylancl
    #
    syl5sseqr
    #
    @56
    @34
    @84
    sstr2
    syl5com
    ralimdv
    @94
    @99
    @97
    @139
    @86
    @99
    vy
    @33
    vn
    vex
    vy
    vn
    weq
    #
    @56
    @34
    @84
    @54
    @33
    @3
    fveq2
    #
    sseq1d
    ralsn
    sylibr
    jctird
    @87
    @86
    vy
    @33
    @96
    cun
    #
    wral
    @98
    @86
    vy
    @83
    @142
    @33
    df-suc
    raleqi
    @86
    vy
    @33
    @96
    ralunb
    bitri
    syl6ibr
    @94
    @84
    @104
    @1
    @138
    @79
    @104
    @1
    wss
    #
    @46
    @79
    @115
    @1
    @103
    wf
    #
    @143
    @79
    @102
    @1
    wcel
    #
    vb
    @34
    wral
    #
    va
    @34
    wral
    #
    @144
    @79
    @145
    vb
    @1
    wral
    #
    va
    @1
    wral
    #
    @147
    @145
    va
    vb
    @1
    @100
    @101
    cA
    fiin
    rgen2a
    @79
    @149
    @146
    va
    @1
    wral
    @147
    @79
    @148
    @146
    va
    @1
    @145
    vb
    @34
    @1
    ssralv
    ralimdv
    @146
    va
    @34
    @1
    ssralv
    syld
    mpi
    va
    vb
    @34
    @34
    @102
    @1
    @103
    @112
    fmpt2
    sylib
    @115
    @1
    @103
    frn
    syl
    adantl
    eqsstrd
    jctild
    expimpd
    a1d
    finds2
    impcom
    #
    simprd
    r19.21bi
    ex
    adantr
    @71
    @58
    wi
    @69
    @71
    @56
    @57
    wceq
    @58
    @54
    @7
    @3
    fveq2
    @56
    @57
    eqimss
    syl
    a1i
    jaod
    sylbid
    ralrimiva
    ralrimiva
    adantr
    #
    @62
    @48
    @30
    @33
    ssun1
    a1i
    @59
    @62
    @63
    wi
    @54
    @49
    wss
    #
    @56
    @50
    wss
    #
    wi
    #
    vx
    vy
    @49
    @30
    com
    com
    @7
    @49
    wceq
    #
    @55
    @152
    @58
    @153
    @7
    @49
    @54
    sseq2
    @155
    @57
    @50
    @56
    @7
    @49
    @3
    fveq2
    sseq2d
    imbi12d
    #
    vy
    vm
    weq
    #
    @152
    @62
    @153
    @63
    @54
    @30
    @49
    sseq1
    @157
    @56
    @31
    @50
    @54
    @30
    @3
    fveq2
    sseq1d
    imbi12d
    rspc2v
    syl3c
    sseld
    @48
    @34
    @50
    @10
    @48
    @53
    @46
    wa
    @61
    @33
    @49
    wss
    #
    @34
    @50
    wss
    #
    @48
    @53
    @46
    @65
    @0
    @45
    @46
    simprr
    jca
    @151
    @158
    @48
    @33
    @30
    ssun2
    a1i
    @59
    @158
    @159
    wi
    @154
    vx
    vy
    @49
    @33
    com
    com
    @156
    @140
    @152
    @158
    @153
    @159
    @54
    @33
    @49
    sseq1
    @140
    @56
    @34
    @50
    @141
    sseq1d
    imbi12d
    rspc2v
    syl3c
    sseld
    @48
    @51
    @52
    wa
    #
    @20
    @48
    @160
    wa
    #
    @11
    vx
    com
    @57
    ciun
    #
    @5
    @161
    @49
    csuc
    #
    @3
    cfv
    #
    @162
    @11
    @161
    @53
    @163
    com
    wcel
    @164
    @162
    wss
    @47
    @53
    @0
    @160
    @64
    ad2antlr
    #
    @49
    peano2
    vx
    com
    @57
    @163
    @164
    @7
    @163
    @3
    fveq2
    ssiun2s
    3syl
    @161
    @11
    va
    vb
    @50
    @50
    @102
    cmpt2
    #
    crn
    #
    @164
    @161
    @11
    @106
    vb
    @50
    wrex
    va
    @50
    wrex
    #
    vx
    cab
    #
    @167
    @161
    @11
    @102
    wceq
    #
    vb
    @50
    wrex
    va
    @50
    wrex
    #
    @11
    @169
    wcel
    @161
    @51
    @52
    @11
    @11
    wceq
    #
    @171
    @48
    @51
    @52
    simprl
    @48
    @51
    @52
    simprr
    @161
    @11
    eqidd
    @170
    @172
    @11
    @9
    @101
    cin
    #
    wceq
    va
    vb
    @9
    @10
    @50
    @50
    va
    vc
    weq
    @102
    @173
    @11
    @100
    @9
    @101
    ineq1
    eqeq2d
    vb
    vd
    weq
    @173
    @11
    @11
    @101
    @10
    @9
    ineq2
    eqeq2d
    rspc2ev
    syl3anc
    @168
    @171
    vx
    @11
    @9
    @10
    vc
    vex
    inex1
    @7
    @11
    wceq
    @106
    @170
    va
    vb
    @50
    @50
    @7
    @11
    @102
    eqeq1
    2rexbidv
    elab
    sylibr
    va
    vb
    vx
    @50
    @50
    @102
    @166
    @166
    eqid
    #
    rnmpt2
    syl6eleqr
    @161
    @53
    @167
    cvv
    wcel
    @164
    @167
    wceq
    @165
    @167
    @50
    cuni
    #
    cpw
    #
    @175
    @50
    @49
    @3
    fvex
    uniex
    pwex
    @50
    @50
    cxp
    #
    @176
    @166
    wf
    #
    @167
    @176
    wss
    @102
    @176
    wcel
    #
    vb
    @50
    wral
    va
    @50
    wral
    @178
    @179
    va
    vb
    @50
    @100
    @50
    wcel
    #
    @179
    @101
    @50
    wcel
    @180
    @102
    @175
    wss
    @179
    @180
    @102
    @100
    @175
    @121
    @100
    @50
    elssuni
    syl5ss
    @102
    @175
    @122
    elpw
    sylibr
    adantr
    rgen2a
    va
    vb
    @50
    @50
    @102
    @176
    @166
    @174
    fmpt2
    mpbi
    @177
    @176
    @166
    frn
    ax-mp
    ssexi
    vv
    cA
    @49
    @125
    @167
    @3
    cvv
    @126
    vv
    @49
    nfcv
    vv
    @167
    nfcv
    @136
    @123
    @50
    wceq
    #
    @124
    @166
    @181
    @124
    @166
    wceq
    va
    vb
    @123
    @123
    @50
    @50
    @102
    mpt2eq12
    anidms
    rneqd
    frsucmpt
    sylancl
    eleqtrrd
    sseldd
    @25
    @162
    @5
    wceq
    @26
    vx
    com
    @3
    fniunfv
    ax-mp
    syl6eleq
    ex
    syl2and
    rexlimdvva
    imp
    sylan2br
    ralrimivva
    @0
    @5
    cvv
    wcel
    #
    @18
    @19
    @22
    wa
    #
    wb
    @0
    @5
    @1
    wss
    #
    @1
    cvv
    wcel
    @182
    @0
    @4
    @1
    cpw
    #
    wss
    #
    @184
    @0
    @25
    @57
    @185
    wcel
    #
    vx
    com
    wral
    @186
    @26
    @0
    @187
    vx
    com
    @67
    @75
    @187
    @67
    @75
    @76
    @150
    simpld
    @57
    @1
    cA
    cfi
    fvex
    #
    elpw2
    sylibr
    ralrimiva
    vx
    com
    @185
    @3
    fnfvrnss
    sylancr
    @4
    @1
    sspwuni
    sylib
    #
    @188
    @5
    @1
    cvv
    ssexg
    sylancl
    @15
    @183
    vx
    @5
    cvv
    @7
    @5
    wceq
    @8
    @19
    @14
    @22
    @7
    @5
    cA
    sseq2
    @13
    @21
    vc
    @7
    @5
    @12
    @20
    vd
    @7
    @5
    @7
    @5
    @11
    eleq2
    raleqbi1dv
    raleqbi1dv
    anbi12d
    elabg
    syl
    mpbir2and
    @5
    @16
    intss1
    syl
    eqsstrd
    @189
    eqssd
    @6
    @4
    @2
    com
    df-ima
    unieqi
    syl6eqr
end
