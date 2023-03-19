include "c1stc.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "cn.mm"
include "cv.mm"
include "wf.mm"
include "clm.mm"
include "wbr.mm"
include "wex.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "w3a.mm"
include "simpll.mm"
include "ctop.mm"
include "1stctop.mm"
include "clsss3.mm"
include "sylan.mm"
include "sselda.mm"
include "1stcfb.mm"
include "syl2anc.mm"
include "cid.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "simpr1.mm"
include "ffvelrnda.mm"
include "wb.mm"
include "elcls2.mm"
include "simplbda.mm"
include "ad2antrr.mm"
include "simpr2.mm"
include "simpl.mm"
include "ralimi.mm"
include "syl.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "rspccva.mm"
include "wceq.mm"
include "eleq2.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "elin.mm"
include "ancom.mm"
include "bitri.mm"
include "exbii.mm"
include "n0.mm"
include "df-rex.mm"
include "3bitr4i.mm"
include "sylib.mm"
include "cvv.mm"
include "topopn.mm"
include "simplr.mm"
include "ssexd.mm"
include "fvi.mm"
include "rexeqdv.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "fvex.mm"
include "nnenom.mm"
include "eleq1.mm"
include "axcc4.mm"
include "feq3d.mm"
include "biimpd.mm"
include "adantr.mm"
include "cuz.mm"
include "simplr3.mm"
include "sseq1d.mm"
include "cbvrexv.mm"
include "sseq2.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "simpr.mm"
include "simprrr.mm"
include "imbi2d.mm"
include "cz.mm"
include "ssid.mm"
include "2a1i.mm"
include "eluznn.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "sseq12d.mm"
include "sylan2.mm"
include "anassrs.mm"
include "sstr2.mm"
include "expcom.mm"
include "a2d.mm"
include "uzind4.mm"
include "com12.mm"
include "ralrimiv.mm"
include "ad2antlr.mm"
include "eleq12d.mm"
include "sylc.mm"
include "r19.26.mm"
include "sylanbrc.mm"
include "ssel2.mm"
include "ssel.mm"
include "ralimdv.mm"
include "syl5com.mm"
include "reximdva.mm"
include "syld.mm"
include "ctopon.mm"
include "toptopon.mm"
include "nnuz.mm"
include "1zzd.mm"
include "simprl.mm"
include "fssd.mm"
include "eqidd.mm"
include "lmbrf.mm"
include "mpbir2and.mm"
include "expr.mm"
include "imdistanda.mm"
include "syland.mm"
include "eximdv.mm"
include "mpd.mm"
include "exlimddv.mm"
include "ex.mm"
include "simprr.mm"
include "lmcls.mm"
include "exlimdv.mm"
include "impbid.mm"

theorem 1stcelcls
  let cP: class P
  let cS: class S
  let vf: setvar f
  let cJ: class J
  let cX: class X
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  assume 1stcelcls.1: |- X = U. J

  disjoint J f
  disjoint P f
  disjoint S f
  disjoint X f
  disjoint f g
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint J g
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint J k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint J m
  disjoint n x
  disjoint n y
  disjoint J n
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint P g
  disjoint P j
  disjoint P k
  disjoint P m
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint S g
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint X g
  disjoint X j
  disjoint X k
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint X y
  assert |- ( ( J e. 1stc /\ S C_ X ) -> ( P e. ( ( cls ` J ) ` S ) <-> E. f ( f : NN --> S /\ f ( ~~>t ` J ) P ) ) )

  proof
    cJ
    c1stc
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cP
    cS
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    cn
    cS
    vf
    cv
    #
    wf
    #
    @5
    cP
    cJ
    clm
    cfv
    wbr
    #
    wa
    #
    vf
    wex
    #
    @2
    @4
    @9
    @2
    @4
    wa
    #
    cn
    cJ
    vg
    cv
    #
    wf
    #
    cP
    vk
    cv
    #
    @11
    cfv
    #
    wcel
    #
    @13
    c1
    caddc
    co
    #
    @11
    cfv
    #
    @14
    wss
    #
    wa
    #
    vk
    cn
    wral
    #
    cP
    vx
    cv
    #
    wcel
    #
    @14
    @21
    wss
    #
    vk
    cn
    wrex
    #
    wi
    #
    vx
    cJ
    wral
    #
    w3a
    #
    @9
    vg
    @10
    @0
    cP
    cX
    wcel
    #
    @27
    vg
    wex
    @0
    @1
    @4
    simpll
    @2
    @3
    cX
    cP
    @0
    cJ
    ctop
    wcel
    #
    @1
    @3
    cX
    wss
    cJ
    1stctop
    #
    cS
    cJ
    cX
    1stcelcls.1
    clsss3
    sylan
    sselda
    #
    vx
    cP
    vg
    vk
    cJ
    cX
    1stcelcls.1
    1stcfb
    syl2anc
    @10
    @27
    wa
    #
    cn
    cS
    cid
    cfv
    #
    @5
    wf
    #
    vn
    cv
    #
    @5
    cfv
    #
    @35
    @11
    cfv
    #
    wcel
    #
    vn
    cn
    wral
    #
    wa
    #
    vf
    wex
    #
    @9
    @32
    @21
    @37
    wcel
    #
    vx
    @33
    wrex
    #
    vn
    cn
    wral
    @41
    @32
    @43
    vn
    cn
    @32
    @35
    cn
    wcel
    #
    wa
    #
    @43
    @42
    vx
    cS
    wrex
    #
    @45
    @37
    cS
    cin
    #
    c0
    wne
    #
    @46
    @45
    @37
    cJ
    wcel
    cP
    vy
    cv
    #
    wcel
    #
    @49
    cS
    cin
    #
    c0
    wne
    #
    wi
    #
    vy
    cJ
    wral
    #
    cP
    @37
    wcel
    #
    @48
    @32
    cn
    cJ
    @35
    @11
    @10
    @12
    @20
    @26
    simpr1
    ffvelrnda
    @10
    @54
    @27
    @44
    @2
    @4
    @28
    @54
    @0
    @29
    @1
    @4
    @28
    @54
    wa
    wb
    @30
    vy
    cP
    cS
    cJ
    cX
    1stcelcls.1
    elcls2
    sylan
    simplbda
    ad2antrr
    @32
    @15
    vk
    cn
    wral
    #
    @44
    @55
    @32
    @20
    @56
    @10
    @12
    @20
    @26
    simpr2
    #
    @19
    @15
    vk
    cn
    @15
    @18
    simpl
    ralimi
    syl
    @15
    @55
    vk
    @35
    cn
    vk
    vn
    weq
    @14
    @37
    cP
    @13
    @35
    @11
    fveq2
    eleq2d
    rspccva
    sylan
    @53
    @55
    @48
    wi
    vy
    @37
    cJ
    @49
    @37
    wceq
    #
    @50
    @55
    @52
    @48
    @49
    @37
    cP
    eleq2
    @58
    @51
    @47
    c0
    @49
    @37
    cS
    ineq1
    neeq1d
    imbi12d
    rspcv
    syl3c
    @21
    @47
    wcel
    #
    vx
    wex
    @21
    cS
    wcel
    #
    @42
    wa
    #
    vx
    wex
    @48
    @46
    @59
    @61
    vx
    @59
    @42
    @60
    wa
    @61
    @21
    @37
    cS
    elin
    @42
    @60
    ancom
    bitri
    exbii
    vx
    @47
    n0
    @42
    vx
    cS
    df-rex
    3bitr4i
    sylib
    @45
    @42
    vx
    @33
    cS
    @10
    @33
    cS
    wceq
    #
    @27
    @44
    @10
    cS
    cvv
    wcel
    @62
    @10
    cS
    cX
    cJ
    @10
    @29
    cX
    cJ
    wcel
    @0
    @29
    @1
    @4
    @30
    ad2antrr
    #
    cJ
    cX
    1stcelcls.1
    topopn
    syl
    @0
    @1
    @4
    simplr
    #
    ssexd
    cS
    cvv
    fvi
    syl
    #
    ad2antrr
    rexeqdv
    mpbird
    ralrimiva
    @42
    @38
    vx
    @33
    vf
    vn
    cn
    cS
    cid
    fvex
    nnenom
    @21
    @36
    @37
    eleq1
    axcc4
    syl
    @32
    @40
    @8
    vf
    @32
    @34
    @6
    @39
    @8
    @10
    @34
    @6
    wi
    @27
    @10
    @34
    @6
    @10
    @33
    cS
    @5
    cn
    @65
    feq3d
    biimpd
    adantr
    @32
    @6
    @39
    @7
    @32
    @6
    @39
    @7
    @32
    @6
    @39
    wa
    #
    wa
    #
    @7
    @28
    @50
    vm
    cv
    #
    @5
    cfv
    #
    @49
    wcel
    #
    vm
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cn
    wrex
    #
    wi
    #
    vy
    cJ
    wral
    @10
    @28
    @27
    @66
    @31
    ad2antrr
    @67
    @75
    vy
    cJ
    @67
    @49
    cJ
    wcel
    #
    wa
    #
    @50
    @71
    @11
    cfv
    #
    @49
    wss
    #
    vj
    cn
    wrex
    #
    @74
    @67
    @26
    @76
    @50
    @80
    wi
    #
    @12
    @20
    @26
    @10
    @66
    simplr3
    @25
    @81
    vx
    @49
    cJ
    vx
    vy
    weq
    #
    @22
    @50
    @24
    @80
    @21
    @49
    cP
    eleq2
    @24
    @78
    @21
    wss
    #
    vj
    cn
    wrex
    @82
    @80
    @23
    @83
    vk
    vj
    cn
    vk
    vj
    weq
    @14
    @78
    @21
    @13
    @71
    @11
    fveq2
    sseq1d
    cbvrexv
    @82
    @83
    @79
    vj
    cn
    @21
    @49
    @78
    sseq2
    rexbidv
    syl5bb
    imbi12d
    rspccva
    sylan
    @77
    @79
    @73
    vj
    cn
    @67
    @76
    @71
    cn
    wcel
    #
    @79
    @73
    wi
    #
    @32
    @66
    @76
    @84
    wa
    #
    @85
    @32
    @66
    @86
    wa
    #
    wa
    #
    @69
    @78
    wcel
    #
    vm
    @72
    wral
    #
    @79
    @73
    @88
    @68
    @11
    cfv
    #
    @78
    wss
    #
    @69
    @91
    wcel
    #
    wa
    #
    vm
    @72
    wral
    #
    @90
    @88
    @92
    vm
    @72
    wral
    #
    @93
    vm
    @72
    wral
    @95
    @88
    @18
    vk
    cn
    wral
    #
    @84
    @96
    @32
    @97
    @87
    @32
    @20
    @97
    @57
    @19
    @18
    vk
    cn
    @15
    @18
    simpr
    ralimi
    syl
    adantr
    @32
    @66
    @76
    @84
    simprrr
    #
    @97
    @84
    wa
    #
    @92
    vm
    @72
    @68
    @72
    wcel
    #
    @99
    @92
    @99
    @37
    @78
    wss
    #
    wi
    @99
    @78
    @78
    wss
    #
    wi
    @99
    @92
    wi
    #
    @99
    @68
    c1
    caddc
    co
    #
    @11
    cfv
    #
    @78
    wss
    #
    wi
    @103
    vn
    vm
    @71
    @68
    vn
    vj
    weq
    #
    @101
    @102
    @99
    @107
    @37
    @78
    @78
    @35
    @71
    @11
    fveq2
    sseq1d
    imbi2d
    vn
    vm
    weq
    #
    @101
    @92
    @99
    @108
    @37
    @91
    @78
    @35
    @68
    @11
    fveq2
    #
    sseq1d
    imbi2d
    #
    @35
    @104
    wceq
    #
    @101
    @106
    @99
    @111
    @37
    @105
    @78
    @35
    @104
    @11
    fveq2
    sseq1d
    imbi2d
    @110
    @102
    @71
    cz
    wcel
    @99
    @78
    ssid
    2a1i
    @100
    @99
    @92
    @106
    @99
    @100
    @92
    @106
    wi
    #
    @99
    @100
    wa
    @105
    @91
    wss
    #
    @112
    @97
    @84
    @100
    @113
    @84
    @100
    wa
    @97
    @68
    cn
    wcel
    #
    @113
    @68
    @71
    eluznn
    #
    @18
    @113
    vk
    @68
    cn
    vk
    vm
    weq
    #
    @17
    @105
    @14
    @91
    @116
    @16
    @104
    @11
    @13
    @68
    c1
    caddc
    oveq1
    fveq2d
    @13
    @68
    @11
    fveq2
    sseq12d
    rspccva
    sylan2
    anassrs
    @105
    @91
    @78
    sstr2
    syl
    expcom
    a2d
    uzind4
    com12
    ralrimiv
    syl2anc
    @88
    @93
    vm
    @72
    @88
    @100
    wa
    @114
    @39
    @93
    @88
    @84
    @100
    @114
    @98
    @115
    sylan
    @87
    @39
    @32
    @100
    @6
    @39
    @86
    simplr
    ad2antlr
    @38
    @93
    vn
    @68
    cn
    @108
    @36
    @69
    @37
    @91
    @35
    @68
    @5
    fveq2
    @109
    eleq12d
    rspcv
    sylc
    ralrimiva
    @92
    @93
    vm
    @72
    r19.26
    sylanbrc
    @94
    @89
    vm
    @72
    @91
    @78
    @69
    ssel2
    ralimi
    syl
    @79
    @89
    @70
    vm
    @72
    @78
    @49
    @69
    ssel
    ralimdv
    syl5com
    anassrs
    anassrs
    reximdva
    syld
    ralrimiva
    @67
    vy
    @69
    cP
    vj
    vm
    @5
    cJ
    c1
    cX
    cn
    @67
    @29
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @10
    @29
    @27
    @66
    @63
    ad2antrr
    cJ
    cX
    1stcelcls.1
    toptopon
    #
    sylib
    nnuz
    @67
    1zzd
    @67
    cn
    cS
    cX
    @5
    @32
    @6
    @39
    simprl
    @10
    @1
    @27
    @66
    @64
    ad2antrr
    fssd
    @67
    @114
    wa
    @69
    eqidd
    lmbrf
    mpbir2and
    expr
    imdistanda
    syland
    eximdv
    mpd
    exlimddv
    ex
    @2
    @8
    @4
    vf
    @2
    @8
    @4
    @2
    @8
    wa
    #
    cP
    cS
    vk
    @5
    cJ
    c1
    cX
    cn
    nnuz
    @119
    @29
    @117
    @0
    @29
    @1
    @8
    @30
    ad2antrr
    @118
    sylib
    @119
    1zzd
    @2
    @6
    @7
    simprr
    @119
    cn
    cS
    @13
    @5
    @2
    @6
    @7
    simprl
    ffvelrnda
    @0
    @1
    @8
    simplr
    lmcls
    ex
    exlimdv
    impbid
end
