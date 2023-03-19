include "cn0.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "c0p.mm"
include "wne.mm"
include "cdgr.mm"
include "cle.mm"
include "wbr.mm"
include "ccoe.mm"
include "cabs.mm"
include "wral.mm"
include "w3a.mm"
include "cz.mm"
include "cply.mm"
include "crab.mm"
include "wrex.mm"
include "cc.mm"
include "cfn.mm"
include "breq2.mm"
include "ralbidv.mm"
include "3anbi23d.mm"
include "rabbidv.mm"
include "rexeqdv.mm"
include "cnex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "ciun.mm"
include "iunrab.mm"
include "cneg.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "cdom.mm"
include "fzfi.mm"
include "mapfi.mm"
include "mp2an.mm"
include "a1i.mm"
include "cvv.mm"
include "ovex.mm"
include "cres.mm"
include "wa.mm"
include "weq.mm"
include "neeq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "3anbi123d.mm"
include "elrab.mm"
include "simp3.mm"
include "anim2i.mm"
include "sylbi.mm"
include "wf.mm"
include "wss.mm"
include "wfn.mm"
include "crn.mm"
include "0z.mm"
include "eqid.mm"
include "coef2.mm"
include "mpan2.mm"
include "ad2antrl.mm"
include "ffnd.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "zred.mm"
include "cr.mm"
include "nn0re.mm"
include "ad2antrr.mm"
include "absled.mm"
include "wb.mm"
include "nn0z.mm"
include "znegcld.mm"
include "elfz.mm"
include "syl3anc.mm"
include "bitr4d.mm"
include "biimpd.mm"
include "ralimdva.mm"
include "impr.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "fz0ssnn0.mm"
include "fssres.mm"
include "sylancl.mm"
include "elmap.mm"
include "sylibr.mm"
include "ex.mm"
include "syl5.mm"
include "simp2.mm"
include "simplll.mm"
include "plyf.mm"
include "ffn.mm"
include "3syl.mm"
include "simplrl.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "simplrr.mm"
include "adantr.mm"
include "fvres.mm"
include "3eqtr3d.mm"
include "oveq1d.mm"
include "sumeq2dv.mm"
include "cuz.mm"
include "simp-4l.mm"
include "simp-4r.mm"
include "dgrcl.mm"
include "nn0zd.mm"
include "eluz.mm"
include "mpbird.mm"
include "simpr.mm"
include "coeid3.mm"
include "simp1rl.mm"
include "3expa.mm"
include "3eqtr4d.mm"
include "eqfnfvd.mm"
include "expr.mm"
include "reseq1d.mm"
include "impbid1.mm"
include "expcom.mm"
include "syl2ani.mm"
include "dom2d.mm"
include "mpi.mm"
include "domfi.mm"
include "simp1.mm"
include "wi.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "fniniseg.mm"
include "syl.mm"
include "eqeq1d.mm"
include "syl6rbbr.mm"
include "eqrdv.mm"
include "chash.mm"
include "fta1.mm"
include "simpld.mm"
include "eqeltrd.mm"
include "ralrimiv.mm"
include "iunfi.mm"
include "syl5eqelr.mm"

theorem aannenlem1
  let cA: class A
  let ve: setvar e
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  assume aannenlem.a: |- H = ( a e. NN0 |-> { b e. CC | E. c e. { d e. ( Poly ` ZZ ) | ( d =/= 0p /\ ( deg ` d ) <_ a /\ A. e e. NN0 ( abs ` ( ( coeff ` d ) ` e ) ) <_ a ) } ( c ` b ) = 0 } )

  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint A e
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint c d
  disjoint c e
  disjoint d e
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A i
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a i
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b i
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c i
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d i
  disjoint e f
  disjoint e g
  disjoint e h
  disjoint e i
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint g h
  disjoint g i
  disjoint h i
  assert |- ( A e. NN0 -> ( H ` A ) e. Fin )

  proof
    cA
    cn0
    wcel
    #
    cA
    cH
    cfv
    vb
    cv
    #
    vc
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    vc
    vd
    cv
    #
    c0p
    wne
    #
    @5
    cdgr
    cfv
    #
    cA
    cle
    wbr
    #
    ve
    cv
    #
    @5
    ccoe
    cfv
    #
    cfv
    #
    cabs
    cfv
    #
    cA
    cle
    wbr
    #
    ve
    cn0
    wral
    #
    w3a
    #
    vd
    cz
    cply
    cfv
    #
    crab
    #
    wrex
    #
    vb
    cc
    crab
    #
    cfn
    va
    cA
    @4
    vc
    @6
    @7
    va
    cv
    #
    cle
    wbr
    #
    @12
    @20
    cle
    wbr
    #
    ve
    cn0
    wral
    #
    w3a
    #
    vd
    @16
    crab
    #
    wrex
    #
    vb
    cc
    crab
    @19
    cn0
    cH
    @20
    cA
    wceq
    #
    @26
    @18
    vb
    cc
    @27
    @4
    vc
    @25
    @17
    @27
    @24
    @15
    vd
    @16
    @27
    @21
    @8
    @23
    @14
    @6
    @20
    cA
    @7
    cle
    breq2
    @27
    @22
    @13
    ve
    cn0
    @20
    cA
    @12
    cle
    breq2
    ralbidv
    3anbi23d
    rabbidv
    rexeqdv
    rabbidv
    aannenlem.a
    @18
    vb
    cc
    cnex
    rabex
    fvmpt
    @0
    @19
    vc
    @17
    @4
    vb
    cc
    crab
    #
    ciun
    #
    cfn
    @4
    vc
    vb
    @17
    cc
    iunrab
    @0
    @17
    cfn
    wcel
    #
    @28
    cfn
    wcel
    #
    vc
    @17
    wral
    @29
    cfn
    wcel
    @0
    cA
    cneg
    #
    cA
    cfz
    co
    #
    cc0
    cA
    cfz
    co
    #
    cmap
    co
    #
    cfn
    wcel
    #
    @17
    @35
    cdom
    wbr
    #
    @30
    @36
    @0
    @33
    cfn
    wcel
    @34
    cfn
    wcel
    @36
    @32
    cA
    fzfi
    cc0
    cA
    fzfi
    @33
    @34
    mapfi
    mp2an
    a1i
    @0
    @35
    cvv
    wcel
    @37
    @33
    @34
    cmap
    ovex
    @0
    va
    vb
    @17
    @35
    @20
    ccoe
    cfv
    #
    @34
    cres
    #
    @1
    ccoe
    cfv
    #
    @34
    cres
    #
    cvv
    @20
    @17
    wcel
    #
    @20
    @16
    wcel
    #
    @9
    @38
    cfv
    #
    cabs
    cfv
    #
    cA
    cle
    wbr
    #
    ve
    cn0
    wral
    #
    wa
    #
    @0
    @39
    @35
    wcel
    #
    @42
    @43
    @20
    c0p
    wne
    #
    @20
    cdgr
    cfv
    #
    cA
    cle
    wbr
    #
    @47
    w3a
    #
    wa
    #
    @48
    @15
    @53
    vd
    @20
    @16
    vd
    va
    weq
    #
    @6
    @50
    @8
    @52
    @14
    @47
    @5
    @20
    c0p
    neeq1
    @55
    @7
    @51
    cA
    cle
    @5
    @20
    cdgr
    fveq2
    breq1d
    @55
    @13
    @46
    ve
    cn0
    @55
    @12
    @45
    cA
    cle
    @55
    @11
    @44
    cabs
    @55
    @9
    @10
    @38
    @5
    @20
    ccoe
    fveq2
    fveq1d
    fveq2d
    breq1d
    ralbidv
    3anbi123d
    elrab
    #
    @53
    @47
    @43
    @50
    @52
    @47
    simp3
    anim2i
    sylbi
    @0
    @48
    @49
    @0
    @48
    wa
    #
    @34
    @33
    @39
    wf
    #
    @49
    @57
    cn0
    @33
    @38
    wf
    #
    @34
    cn0
    wss
    @58
    @57
    @38
    cn0
    wfn
    #
    @38
    crn
    @33
    wss
    #
    @59
    @57
    cn0
    cz
    @38
    @43
    cn0
    cz
    @38
    wf
    #
    @0
    @47
    @43
    cc0
    cz
    wcel
    @62
    0z
    @38
    cz
    @20
    @38
    eqid
    #
    coef2
    mpan2
    #
    ad2antrl
    ffnd
    #
    @57
    @60
    @44
    @33
    wcel
    #
    ve
    cn0
    wral
    #
    @61
    @65
    @0
    @43
    @47
    @67
    @0
    @43
    wa
    #
    @46
    @66
    ve
    cn0
    @68
    @9
    cn0
    wcel
    #
    wa
    #
    @46
    @66
    @70
    @46
    @32
    @44
    cle
    wbr
    @44
    cA
    cle
    wbr
    wa
    #
    @66
    @70
    @44
    cA
    @70
    @44
    @68
    cn0
    cz
    @9
    @38
    @43
    @62
    @0
    @64
    adantl
    ffvelrnda
    #
    zred
    @0
    cA
    cr
    wcel
    @43
    @69
    cA
    nn0re
    ad2antrr
    absled
    @70
    @44
    cz
    wcel
    @32
    cz
    wcel
    cA
    cz
    wcel
    #
    @66
    @71
    wb
    @72
    @70
    cA
    @0
    @73
    @43
    @69
    cA
    nn0z
    ad2antrr
    #
    znegcld
    @74
    @44
    @32
    cA
    elfz
    syl3anc
    bitr4d
    biimpd
    ralimdva
    impr
    ve
    cn0
    @33
    @38
    fnfvrnss
    syl2anc
    cn0
    @33
    @38
    df-f
    sylanbrc
    cA
    fz0ssnn0
    cn0
    @33
    @34
    @38
    fssres
    sylancl
    @33
    @34
    @39
    @32
    cA
    cfz
    ovex
    cc0
    cA
    cfz
    ovex
    elmap
    sylibr
    ex
    syl5
    @42
    @0
    @43
    @52
    wa
    #
    @1
    @16
    wcel
    #
    @1
    cdgr
    cfv
    #
    cA
    cle
    wbr
    #
    wa
    #
    @39
    @41
    wceq
    #
    va
    vb
    weq
    #
    wb
    #
    @1
    @17
    wcel
    #
    @42
    @54
    @75
    @56
    @53
    @52
    @43
    @50
    @52
    @47
    simp2
    anim2i
    sylbi
    @83
    @76
    @1
    c0p
    wne
    #
    @78
    @9
    @40
    cfv
    #
    cabs
    cfv
    #
    cA
    cle
    wbr
    #
    ve
    cn0
    wral
    #
    w3a
    #
    wa
    @79
    @15
    @89
    vd
    @1
    @16
    vd
    vb
    weq
    #
    @6
    @84
    @8
    @78
    @14
    @88
    @5
    @1
    c0p
    neeq1
    @90
    @7
    @77
    cA
    cle
    @5
    @1
    cdgr
    fveq2
    breq1d
    @90
    @13
    @87
    ve
    cn0
    @90
    @12
    @86
    cA
    cle
    @90
    @11
    @85
    cabs
    @90
    @9
    @10
    @40
    @5
    @1
    ccoe
    fveq2
    fveq1d
    fveq2d
    breq1d
    ralbidv
    3anbi123d
    elrab
    @89
    @78
    @76
    @84
    @78
    @88
    simp2
    anim2i
    sylbi
    @75
    @79
    wa
    #
    @0
    @82
    @91
    @0
    wa
    @80
    @81
    @91
    @0
    @80
    @81
    @91
    @0
    @80
    wa
    #
    wa
    #
    vc
    cc
    @20
    @1
    @93
    @43
    cc
    cc
    @20
    wf
    @20
    cc
    wfn
    @43
    @52
    @79
    @92
    simplll
    cz
    @20
    plyf
    cc
    cc
    @20
    ffn
    3syl
    @93
    @76
    cc
    cc
    @1
    wf
    @1
    cc
    wfn
    @75
    @76
    @78
    @92
    simplrl
    cz
    @1
    plyf
    cc
    cc
    @1
    ffn
    3syl
    @93
    @2
    cc
    wcel
    #
    wa
    #
    @34
    @5
    @38
    cfv
    #
    @2
    @5
    cexp
    co
    #
    cmul
    co
    #
    vd
    csu
    #
    @34
    @5
    @40
    cfv
    #
    @97
    cmul
    co
    #
    vd
    csu
    #
    @2
    @20
    cfv
    #
    @2
    @1
    cfv
    #
    @95
    @34
    @98
    @101
    vd
    @95
    @5
    @34
    wcel
    #
    wa
    #
    @96
    @100
    @97
    cmul
    @106
    @5
    @39
    cfv
    #
    @5
    @41
    cfv
    #
    @96
    @100
    @106
    @5
    @39
    @41
    @95
    @80
    @105
    @91
    @0
    @80
    @94
    simplrr
    adantr
    fveq1d
    @105
    @107
    @96
    wceq
    @95
    @5
    @34
    @38
    fvres
    adantl
    @105
    @108
    @100
    wceq
    @95
    @5
    @34
    @40
    fvres
    adantl
    3eqtr3d
    oveq1d
    sumeq2dv
    @95
    @43
    cA
    @51
    cuz
    cfv
    wcel
    #
    @94
    @103
    @99
    wceq
    @43
    @52
    @79
    @92
    @94
    simp-4l
    #
    @95
    @109
    @52
    @43
    @52
    @79
    @92
    @94
    simp-4r
    @95
    @51
    cz
    wcel
    #
    @73
    @109
    @52
    wb
    @95
    @43
    @51
    cn0
    wcel
    @111
    @110
    cz
    @20
    dgrcl
    @51
    nn0z
    3syl
    @95
    cA
    @91
    @0
    @80
    @94
    simplrl
    nn0zd
    #
    @51
    cA
    eluz
    syl2anc
    mpbird
    @93
    @94
    simpr
    #
    @38
    cz
    vd
    @20
    cA
    @51
    @2
    @63
    @51
    eqid
    coeid3
    syl3anc
    @95
    @76
    cA
    @77
    cuz
    cfv
    wcel
    #
    @94
    @104
    @102
    wceq
    @91
    @92
    @94
    @76
    @76
    @78
    @75
    @92
    @94
    simp1rl
    3expa
    #
    @95
    @114
    @78
    @93
    @78
    @94
    @75
    @76
    @78
    @92
    simplrr
    adantr
    @95
    @77
    cz
    wcel
    #
    @73
    @114
    @78
    wb
    @95
    @76
    @77
    cn0
    wcel
    @116
    @115
    cz
    @1
    dgrcl
    @77
    nn0z
    3syl
    @112
    @77
    cA
    eluz
    syl2anc
    mpbird
    @113
    @40
    cz
    vd
    @1
    cA
    @77
    @2
    @40
    eqid
    @77
    eqid
    coeid3
    syl3anc
    3eqtr4d
    eqfnfvd
    expr
    @81
    @38
    @40
    @34
    @20
    @1
    ccoe
    fveq2
    reseq1d
    impbid1
    expcom
    syl2ani
    dom2d
    mpi
    @35
    @17
    domfi
    syl2anc
    @0
    @31
    vc
    @17
    @2
    @17
    wcel
    #
    @2
    @16
    wcel
    #
    @2
    c0p
    wne
    #
    wa
    #
    @0
    @31
    @117
    @118
    @119
    @2
    cdgr
    cfv
    #
    cA
    cle
    wbr
    #
    @9
    @2
    ccoe
    cfv
    #
    cfv
    #
    cabs
    cfv
    #
    cA
    cle
    wbr
    #
    ve
    cn0
    wral
    #
    w3a
    #
    wa
    @120
    @15
    @128
    vd
    @2
    @16
    vd
    vc
    weq
    #
    @6
    @119
    @8
    @122
    @14
    @127
    @5
    @2
    c0p
    neeq1
    @129
    @7
    @121
    cA
    cle
    @5
    @2
    cdgr
    fveq2
    breq1d
    @129
    @13
    @126
    ve
    cn0
    @129
    @12
    @125
    cA
    cle
    @129
    @11
    @124
    cabs
    @129
    @9
    @10
    @123
    @5
    @2
    ccoe
    fveq2
    fveq1d
    fveq2d
    breq1d
    ralbidv
    3anbi123d
    elrab
    @128
    @119
    @118
    @119
    @122
    @127
    simp1
    anim2i
    sylbi
    @120
    @31
    wi
    @0
    @120
    @28
    @2
    ccnv
    cc0
    csn
    cima
    #
    cfn
    @120
    va
    @28
    @130
    @120
    @20
    @130
    wcel
    #
    @20
    cc
    wcel
    @20
    @2
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    @20
    @28
    wcel
    @120
    @2
    cc
    wfn
    #
    @131
    @134
    wb
    @118
    @135
    @119
    @118
    cc
    cc
    @2
    cz
    @2
    plyf
    ffnd
    adantr
    cc
    cc0
    @20
    @2
    fniniseg
    syl
    @4
    @133
    vb
    @20
    cc
    vb
    va
    weq
    @3
    @132
    cc0
    @1
    @20
    @2
    fveq2
    eqeq1d
    elrab
    syl6rbbr
    eqrdv
    @120
    @130
    cfn
    wcel
    @130
    chash
    cfv
    @121
    cle
    wbr
    @130
    cz
    @2
    @130
    eqid
    fta1
    simpld
    eqeltrd
    a1i
    syl5
    ralrimiv
    vc
    @17
    @28
    iunfi
    syl2anc
    syl5eqelr
    eqeltrd
end
