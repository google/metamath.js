include "cn.mm"
include "cvol.mm"
include "cdm.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "cr.mm"
include "wcel.mm"
include "crn.mm"
include "cuni.mm"
include "cima.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "cfzo.mm"
include "ciun.mm"
include "cdif.mm"
include "cmpt.mm"
include "cseq.mm"
include "wdisj.mm"
include "ffvelrn.mm"
include "ad2ant2r.mm"
include "cfn.mm"
include "fzofi.mm"
include "simpll.mm"
include "cuz.mm"
include "elfzouz.mm"
include "nnuz.mm"
include "syl6eleqr.mm"
include "syl2an.mm"
include "ralrimiva.mm"
include "finiunmbl.mm"
include "sylancr.mm"
include "difmbl.mm"
include "syl2anc.mm"
include "covol.mm"
include "mblvol.mm"
include "syl.mm"
include "difssd.mm"
include "mblss.mm"
include "simprr.mm"
include "eqeltrrd.mm"
include "ovolsscl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "jca.mm"
include "expr.mm"
include "ralimdva.mm"
include "imp.mm"
include "fveq2.mm"
include "iundisj2.mm"
include "eqid.mm"
include "voliun.mm"
include "sylancl.mm"
include "iundisj.mm"
include "wfn.mm"
include "ffn.mm"
include "ad2antrr.mm"
include "fniunfv.mm"
include "syl5eqr.mm"
include "fveq2d.mm"
include "ccom.mm"
include "cz.mm"
include "1z.mm"
include "seqfn.mm"
include "ax-mp.mm"
include "fneq2i.mm"
include "mpbir.mm"
include "a1i.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "volf.mm"
include "fco.mm"
include "wi.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "seq1.mm"
include "1nn.mm"
include "c0.mm"
include "oveq2.mm"
include "fzo0.mm"
include "syl6eq.mm"
include "iuneq1d.mm"
include "0iun.mm"
include "difeq2d.mm"
include "dif0.mm"
include "eqtrd.mm"
include "fvex.mm"
include "fvmpt.mm"
include "eqtri.mm"
include "oveq1.mm"
include "seqp1.mm"
include "eleq2s.mm"
include "adantl.mm"
include "cun.mm"
include "undif2.mm"
include "simpr.mm"
include "simpllr.mm"
include "sseq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "ssequn1.mm"
include "sylib.mm"
include "syl5req.mm"
include "cin.mm"
include "simplll.mm"
include "ffvelrnd.mm"
include "peano2nn.mm"
include "disjdif.mm"
include "simplr.mm"
include "eleq1d.mm"
include "volun.mm"
include "syl32anc.mm"
include "cfz.mm"
include "adantr.mm"
include "elfznn.mm"
include "elfzuz3.mm"
include "volsuplem.mm"
include "syl12anc.mm"
include "iunss.mm"
include "sylibr.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "ssiun2s.mm"
include "eqssd.mm"
include "nnzd.mm"
include "fzval3.mm"
include "eqtr3d.mm"
include "difeq12d.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"
include "fvco3.mm"
include "sylan.mm"
include "eqfnfvd.mm"
include "rneqd.mm"
include "rnco2.mm"
include "supeq1d.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "wn.mm"
include "wrex.mm"
include "rexnal.mm"
include "cle.mm"
include "wbr.mm"
include "iunmbl.mm"
include "ovolcl.mm"
include "pnfge.mm"
include "cmnf.mm"
include "wb.mm"
include "xrrebnd.mm"
include "ovolge0.mm"
include "mnflt0.mm"
include "mnfxr.mm"
include "0xr.mm"
include "xrltletr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "biantrurd.mm"
include "3bitr4d.mm"
include "mtbid.mm"
include "nltpnft.mm"
include "mpbird.mm"
include "simprl.mm"
include "fnfvelrn.mm"
include "elssuni.mm"
include "ovolss.mm"
include "eqbrtrrd.mm"
include "pnfxr.mm"
include "xrletri3.mm"
include "mpbir2and.mm"
include "imassrn.mm"
include "frn.mm"
include "iccssxr.mm"
include "sstri.mm"
include "wfun.mm"
include "ffun.mm"
include "funfvima2.mm"
include "supxrpnf.mm"
include "3eqtr4d.mm"
include "rexlimdvaa.mm"
include "syl5bir.mm"
include "pm2.61d.mm"

theorem volsup
  let vn: setvar n
  let cF: class F
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x

  disjoint F n
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint F k
  disjoint m n
  disjoint m x
  disjoint F m
  disjoint n x
  disjoint F x
  assert |- ( ( F : NN --> dom vol /\ A. n e. NN ( F ` n ) C_ ( F ` ( n + 1 ) ) ) -> ( vol ` U. ran F ) = sup ( ( vol " ran F ) , RR* , < ) )

  proof
    cn
    cvol
    cdm
    #
    cF
    wf
    #
    vn
    cv
    #
    cF
    cfv
    #
    @2
    c1
    caddc
    co
    #
    cF
    cfv
    #
    wss
    #
    vn
    cn
    wral
    #
    wa
    #
    vk
    cv
    #
    cF
    cfv
    #
    cvol
    cfv
    #
    cr
    wcel
    #
    vk
    cn
    wral
    #
    cF
    crn
    #
    cuni
    #
    cvol
    cfv
    #
    cvol
    @14
    cima
    #
    cxr
    clt
    csup
    #
    wceq
    #
    @8
    @13
    @19
    @8
    @13
    wa
    #
    vk
    cn
    @10
    vm
    c1
    @9
    cfzo
    co
    #
    vm
    cv
    #
    cF
    cfv
    #
    ciun
    #
    cdif
    #
    ciun
    #
    cvol
    cfv
    #
    caddc
    vk
    cn
    @25
    cvol
    cfv
    #
    cmpt
    #
    c1
    cseq
    #
    crn
    #
    cxr
    clt
    csup
    #
    @16
    @18
    @20
    @25
    @0
    wcel
    #
    @28
    cr
    wcel
    #
    wa
    #
    vk
    cn
    wral
    #
    vk
    cn
    @25
    wdisj
    @27
    @32
    wceq
    @8
    @13
    @36
    @8
    @12
    @35
    vk
    cn
    @8
    @9
    cn
    wcel
    #
    @12
    @35
    @8
    @37
    @12
    wa
    #
    wa
    #
    @33
    @34
    @39
    @10
    @0
    wcel
    #
    @24
    @0
    wcel
    #
    @33
    @1
    @37
    @40
    @7
    @12
    cn
    @0
    @9
    cF
    ffvelrn
    #
    ad2ant2r
    #
    @39
    @21
    cfn
    wcel
    @23
    @0
    wcel
    #
    vm
    @21
    wral
    @41
    c1
    @9
    fzofi
    @39
    @44
    vm
    @21
    @39
    @1
    @22
    cn
    wcel
    #
    @44
    @22
    @21
    wcel
    #
    @1
    @7
    @38
    simpll
    @46
    @22
    c1
    cuz
    cfv
    #
    cn
    @22
    c1
    @9
    elfzouz
    nnuz
    syl6eleqr
    cn
    @0
    @22
    cF
    ffvelrn
    syl2an
    ralrimiva
    @21
    @23
    vm
    finiunmbl
    sylancr
    @10
    @24
    difmbl
    syl2anc
    #
    @39
    @28
    @25
    covol
    cfv
    #
    cr
    @39
    @33
    @28
    @49
    wceq
    @48
    @25
    mblvol
    syl
    @39
    @25
    @10
    wss
    @10
    cr
    wss
    #
    @10
    covol
    cfv
    #
    cr
    wcel
    #
    @49
    cr
    wcel
    @39
    @10
    @24
    difssd
    @39
    @40
    @50
    @43
    @10
    mblss
    #
    syl
    @39
    @11
    @51
    cr
    @39
    @40
    @11
    @51
    wceq
    #
    @43
    @10
    mblvol
    #
    syl
    @8
    @37
    @12
    simprr
    eqeltrrd
    @25
    @10
    ovolsscl
    syl3anc
    eqeltrd
    jca
    expr
    ralimdva
    imp
    @10
    @23
    vm
    vk
    @9
    @22
    cF
    fveq2
    #
    iundisj2
    @25
    @30
    vk
    @29
    @30
    eqid
    @29
    eqid
    #
    voliun
    sylancl
    @20
    @26
    @15
    cvol
    @20
    @26
    vk
    cn
    @10
    ciun
    #
    @15
    @10
    @23
    vm
    vk
    @56
    iundisj
    @20
    cF
    cn
    wfn
    #
    @58
    @15
    wceq
    @1
    @59
    @7
    @13
    cn
    @0
    cF
    ffn
    #
    ad2antrr
    vk
    cn
    cF
    fniunfv
    syl
    syl5eqr
    fveq2d
    @20
    cxr
    @31
    @17
    clt
    @20
    @31
    cvol
    cF
    ccom
    #
    crn
    @17
    @20
    @30
    @61
    @20
    vj
    cn
    @30
    @61
    @30
    cn
    wfn
    #
    @20
    @62
    @30
    @47
    wfn
    #
    c1
    cz
    wcel
    #
    @63
    1z
    caddc
    @29
    c1
    seqfn
    ax-mp
    cn
    @47
    @30
    nnuz
    fneq2i
    mpbir
    a1i
    @20
    cn
    cc0
    cpnf
    cicc
    co
    #
    @61
    wf
    #
    @61
    cn
    wfn
    @20
    @0
    @65
    cvol
    wf
    #
    @1
    @66
    volf
    @1
    @7
    @13
    simpll
    #
    cn
    @0
    @65
    cvol
    cF
    fco
    sylancr
    cn
    @65
    @61
    ffn
    syl
    @20
    vj
    cv
    #
    cn
    wcel
    #
    wa
    #
    @69
    @30
    cfv
    #
    @69
    cF
    cfv
    #
    cvol
    cfv
    #
    @69
    @61
    cfv
    #
    @70
    @20
    @72
    @74
    wceq
    #
    @20
    vx
    cv
    #
    @30
    cfv
    #
    @77
    cF
    cfv
    #
    cvol
    cfv
    #
    wceq
    #
    wi
    @20
    c1
    @30
    cfv
    #
    c1
    cF
    cfv
    #
    cvol
    cfv
    #
    wceq
    #
    wi
    @20
    @76
    wi
    #
    @20
    @69
    c1
    caddc
    co
    #
    @30
    cfv
    #
    @87
    cF
    cfv
    #
    cvol
    cfv
    #
    wceq
    #
    wi
    @86
    vx
    vj
    @69
    @77
    c1
    wceq
    #
    @81
    @85
    @20
    @92
    @78
    @82
    @80
    @84
    @77
    c1
    @30
    fveq2
    @92
    @79
    @83
    cvol
    @77
    c1
    cF
    fveq2
    fveq2d
    eqeq12d
    imbi2d
    vx
    vj
    weq
    #
    @81
    @76
    @20
    @93
    @78
    @72
    @80
    @74
    @77
    @69
    @30
    fveq2
    @93
    @79
    @73
    cvol
    @77
    @69
    cF
    fveq2
    fveq2d
    eqeq12d
    imbi2d
    #
    @77
    @87
    wceq
    #
    @81
    @91
    @20
    @95
    @78
    @88
    @80
    @90
    @77
    @87
    @30
    fveq2
    @95
    @79
    @89
    cvol
    @77
    @87
    cF
    fveq2
    fveq2d
    eqeq12d
    imbi2d
    @94
    @85
    @20
    @82
    c1
    @29
    cfv
    #
    @84
    @64
    @82
    @96
    wceq
    1z
    caddc
    @29
    c1
    seq1
    ax-mp
    c1
    cn
    wcel
    @96
    @84
    wceq
    1nn
    vk
    c1
    @28
    @84
    cn
    @29
    @9
    c1
    wceq
    #
    @25
    @83
    cvol
    @97
    @25
    @10
    @83
    @97
    @25
    @10
    c0
    cdif
    @10
    @97
    @24
    c0
    @10
    @97
    @24
    vm
    c0
    @23
    ciun
    c0
    @97
    vm
    @21
    c0
    @23
    @97
    @21
    c1
    c1
    cfzo
    co
    c0
    @9
    c1
    c1
    cfzo
    oveq2
    c1
    fzo0
    syl6eq
    iuneq1d
    vm
    @23
    0iun
    syl6eq
    difeq2d
    @10
    dif0
    syl6eq
    @9
    c1
    cF
    fveq2
    eqtrd
    fveq2d
    @57
    @83
    cvol
    fvex
    fvmpt
    ax-mp
    eqtri
    a1i
    @70
    @20
    @76
    @91
    @20
    @70
    @76
    @91
    wi
    @76
    @91
    @71
    @72
    @87
    @29
    cfv
    #
    caddc
    co
    #
    @74
    @98
    caddc
    co
    #
    wceq
    @72
    @74
    @98
    caddc
    oveq1
    @71
    @88
    @99
    @90
    @100
    @70
    @88
    @99
    wceq
    #
    @20
    @101
    @69
    @47
    cn
    caddc
    @29
    c1
    @69
    seqp1
    nnuz
    eleq2s
    adantl
    @71
    @90
    @73
    @89
    @73
    cdif
    #
    cun
    #
    cvol
    cfv
    #
    @74
    @102
    cvol
    cfv
    #
    caddc
    co
    #
    @100
    @71
    @89
    @103
    cvol
    @71
    @103
    @73
    @89
    cun
    #
    @89
    @73
    @89
    undif2
    @71
    @73
    @89
    wss
    #
    @107
    @89
    wceq
    @71
    @70
    @7
    @108
    @20
    @70
    simpr
    #
    @1
    @7
    @13
    @70
    simpllr
    #
    @6
    @108
    vn
    @69
    cn
    vn
    vj
    weq
    #
    @3
    @73
    @5
    @89
    @2
    @69
    cF
    fveq2
    @111
    @4
    @87
    cF
    @2
    @69
    c1
    caddc
    oveq1
    fveq2d
    sseq12d
    rspcv
    sylc
    @73
    @89
    ssequn1
    sylib
    syl5req
    fveq2d
    @71
    @73
    @0
    wcel
    #
    @102
    @0
    wcel
    #
    @73
    @102
    cin
    c0
    wceq
    #
    @74
    cr
    wcel
    #
    @105
    cr
    wcel
    @104
    @106
    wceq
    @71
    cn
    @0
    @69
    cF
    @1
    @7
    @13
    @70
    simplll
    #
    @109
    ffvelrnd
    #
    @71
    @89
    @0
    wcel
    #
    @112
    @113
    @71
    cn
    @0
    @87
    cF
    @116
    @70
    @87
    cn
    wcel
    #
    @20
    @69
    peano2nn
    adantl
    #
    ffvelrnd
    #
    @117
    @89
    @73
    difmbl
    syl2anc
    #
    @114
    @71
    @73
    @89
    disjdif
    a1i
    @71
    @70
    @13
    @115
    @109
    @8
    @13
    @70
    simplr
    #
    @12
    @115
    vk
    @69
    cn
    vk
    vj
    weq
    #
    @11
    @74
    cr
    @124
    @10
    @73
    cvol
    @9
    @69
    cF
    fveq2
    fveq2d
    eleq1d
    rspcv
    sylc
    @71
    @105
    @102
    covol
    cfv
    #
    cr
    @71
    @113
    @105
    @125
    wceq
    @122
    @102
    mblvol
    syl
    @71
    @102
    @89
    wss
    @89
    cr
    wss
    #
    @89
    covol
    cfv
    #
    cr
    wcel
    @125
    cr
    wcel
    @71
    @89
    @73
    difssd
    @71
    @118
    @126
    @121
    @89
    mblss
    syl
    @71
    @90
    @127
    cr
    @71
    @118
    @90
    @127
    wceq
    @121
    @89
    mblvol
    syl
    @71
    @119
    @13
    @90
    cr
    wcel
    #
    @120
    @123
    @12
    @128
    vk
    @87
    cn
    @9
    @87
    wceq
    #
    @11
    @90
    cr
    @129
    @10
    @89
    cvol
    @9
    @87
    cF
    fveq2
    #
    fveq2d
    eleq1d
    rspcv
    sylc
    eqeltrrd
    @102
    @89
    ovolsscl
    syl3anc
    eqeltrd
    @73
    @102
    volun
    syl32anc
    @71
    @105
    @98
    @74
    caddc
    @71
    @105
    @89
    vm
    c1
    @87
    cfzo
    co
    #
    @23
    ciun
    #
    cdif
    #
    cvol
    cfv
    #
    @98
    @71
    @102
    @133
    cvol
    @71
    @73
    @132
    @89
    @71
    vm
    c1
    @69
    cfz
    co
    #
    @23
    ciun
    #
    @73
    @132
    @71
    @136
    @73
    @71
    @23
    @73
    wss
    #
    vm
    @135
    wral
    @136
    @73
    wss
    @71
    @137
    vm
    @135
    @71
    @22
    @135
    wcel
    #
    wa
    @7
    @45
    @69
    @22
    cuz
    cfv
    wcel
    #
    @137
    @71
    @7
    @138
    @110
    adantr
    @138
    @45
    @71
    @22
    @69
    elfznn
    adantl
    @138
    @139
    @71
    @22
    c1
    @69
    elfzuz3
    adantl
    @22
    @69
    vn
    cF
    volsuplem
    syl12anc
    ralrimiva
    vm
    @135
    @23
    @73
    iunss
    sylibr
    @71
    @69
    @135
    wcel
    #
    @73
    @136
    wss
    @71
    @69
    @47
    wcel
    @140
    @71
    @69
    cn
    @47
    @109
    nnuz
    syl6eleq
    c1
    @69
    eluzfz2
    syl
    vm
    @135
    @23
    @69
    @73
    @22
    @69
    cF
    fveq2
    ssiun2s
    syl
    eqssd
    @71
    vm
    @135
    @131
    @23
    @71
    @69
    cz
    wcel
    @135
    @131
    wceq
    @71
    @69
    @109
    nnzd
    c1
    @69
    fzval3
    syl
    iuneq1d
    eqtr3d
    difeq2d
    fveq2d
    @71
    @119
    @98
    @134
    wceq
    @120
    vk
    @87
    @28
    @134
    cn
    @29
    @129
    @25
    @133
    cvol
    @129
    @10
    @89
    @24
    @132
    @130
    @129
    vm
    @21
    @131
    @23
    @9
    @87
    c1
    cfzo
    oveq2
    iuneq1d
    difeq12d
    fveq2d
    @57
    @133
    cvol
    fvex
    fvmpt
    syl
    eqtr4d
    oveq2d
    3eqtrd
    eqeq12d
    syl5ibr
    expcom
    a2d
    nnind
    impcom
    @20
    @1
    @70
    @75
    @74
    wceq
    @68
    cn
    @0
    @69
    cvol
    cF
    fvco3
    sylan
    eqtr4d
    eqfnfvd
    rneqd
    cvol
    cF
    rnco2
    syl6eq
    supeq1d
    3eqtr3d
    ex
    @13
    wn
    @12
    wn
    #
    vk
    cn
    wrex
    @8
    @19
    @12
    vk
    cn
    rexnal
    @8
    @141
    @19
    vk
    cn
    @8
    @37
    @141
    wa
    #
    wa
    #
    @15
    covol
    cfv
    #
    cpnf
    @16
    @18
    @143
    @144
    cpnf
    wceq
    #
    @144
    cpnf
    cle
    wbr
    #
    cpnf
    @144
    cle
    wbr
    #
    @143
    @144
    cxr
    wcel
    #
    @146
    @143
    @15
    cr
    wss
    #
    @148
    @143
    @15
    @0
    wcel
    #
    @149
    @1
    @150
    @7
    @142
    @1
    vn
    cn
    @3
    ciun
    #
    @15
    @0
    @1
    @59
    @151
    @15
    wceq
    @60
    vn
    cn
    cF
    fniunfv
    syl
    @1
    @3
    @0
    wcel
    #
    vn
    cn
    wral
    @151
    @0
    wcel
    @1
    @152
    vn
    cn
    cn
    @0
    @2
    cF
    ffvelrn
    ralrimiva
    @3
    vn
    iunmbl
    syl
    eqeltrrd
    ad2antrr
    #
    @15
    mblss
    syl
    #
    @15
    ovolcl
    syl
    #
    @144
    pnfge
    syl
    @143
    @51
    cpnf
    @144
    cle
    @143
    @51
    cpnf
    wceq
    #
    @51
    cpnf
    clt
    wbr
    #
    wn
    #
    @143
    @12
    @157
    @8
    @37
    @141
    simprr
    @143
    @52
    cmnf
    @51
    clt
    wbr
    #
    @157
    wa
    #
    @12
    @157
    @143
    @51
    cxr
    wcel
    #
    @52
    @160
    wb
    @143
    @50
    @161
    @143
    @40
    @50
    @1
    @37
    @40
    @7
    @141
    @42
    ad2ant2r
    #
    @53
    syl
    #
    @10
    ovolcl
    #
    syl
    #
    @51
    xrrebnd
    syl
    @143
    @11
    @51
    cr
    @143
    @40
    @54
    @162
    @55
    syl
    #
    eleq1d
    @143
    @159
    @157
    @143
    @50
    @159
    @163
    @50
    @161
    cc0
    @51
    cle
    wbr
    #
    @159
    @164
    @10
    ovolge0
    @161
    cmnf
    cc0
    clt
    wbr
    #
    @167
    @159
    mnflt0
    cmnf
    cxr
    wcel
    cc0
    cxr
    wcel
    @161
    @168
    @167
    wa
    @159
    wi
    mnfxr
    0xr
    cmnf
    cc0
    @51
    xrltletr
    mp3an12
    mpani
    sylc
    syl
    biantrurd
    3bitr4d
    mtbid
    @143
    @161
    @156
    @158
    wb
    @165
    @51
    nltpnft
    syl
    mpbird
    #
    @143
    @10
    @15
    wss
    #
    @149
    @51
    @144
    cle
    wbr
    @143
    @10
    @14
    wcel
    #
    @170
    @143
    @59
    @37
    @171
    @1
    @59
    @7
    @142
    @60
    ad2antrr
    @8
    @37
    @141
    simprl
    cn
    @9
    cF
    fnfvelrn
    syl2anc
    #
    @10
    @14
    elssuni
    syl
    @154
    @10
    @15
    ovolss
    syl2anc
    eqbrtrrd
    @143
    @148
    cpnf
    cxr
    wcel
    @145
    @146
    @147
    wa
    wb
    @155
    pnfxr
    @144
    cpnf
    xrletri3
    sylancl
    mpbir2and
    @143
    @150
    @16
    @144
    wceq
    @153
    @15
    mblvol
    syl
    @143
    @17
    cxr
    wss
    cpnf
    @17
    wcel
    @18
    cpnf
    wceq
    @17
    cvol
    crn
    #
    cxr
    cvol
    @14
    imassrn
    @173
    @65
    cxr
    @67
    @173
    @65
    wss
    volf
    @0
    @65
    cvol
    frn
    ax-mp
    cc0
    cpnf
    iccssxr
    sstri
    sstri
    @143
    @11
    cpnf
    @17
    @143
    @11
    @51
    cpnf
    @166
    @169
    eqtrd
    @143
    @1
    @171
    @11
    @17
    wcel
    #
    @1
    @7
    @142
    simpll
    @172
    @1
    cvol
    wfun
    #
    @14
    @0
    wss
    @171
    @174
    wi
    @67
    @175
    volf
    @0
    @65
    cvol
    ffun
    ax-mp
    cn
    @0
    cF
    frn
    @14
    @10
    cvol
    funfvima2
    sylancr
    sylc
    eqeltrrd
    @17
    supxrpnf
    sylancr
    3eqtr4d
    rexlimdvaa
    syl5bir
    pm2.61d
end
