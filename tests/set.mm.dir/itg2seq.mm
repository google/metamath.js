include "cr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cn.mm"
include "citg1.mm"
include "cdm.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "citg2.mm"
include "wceq.mm"
include "c1.mm"
include "cdiv.mm"
include "cmin.mm"
include "cif.mm"
include "clt.mm"
include "wa.mm"
include "wral.mm"
include "wex.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "csup.mm"
include "w3a.mm"
include "wrex.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "nnre.mm"
include "ad2antlr.mm"
include "ltpnf.mm"
include "syl.mm"
include "iftrue.mm"
include "adantl.mm"
include "simpr.mm"
include "3brtr4d.mm"
include "iffalse.mm"
include "cmnf.mm"
include "wb.mm"
include "itg2cl.mm"
include "xrrebnd.mm"
include "itg2ge0.mm"
include "mnflt0.mm"
include "mnfxr.mm"
include "0xr.mm"
include "xrltletr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "mpd.mm"
include "biantrurd.mm"
include "nltpnft.mm"
include "con2bid.mm"
include "3bitr2rd.mm"
include "biimpa.mm"
include "adantlr.mm"
include "crp.mm"
include "nnrp.mm"
include "rpreccld.mm"
include "ltsubrpd.mm"
include "eqbrtrd.mm"
include "pm2.61dan.mm"
include "nnrecre.mm"
include "resubcld.mm"
include "ifclda.mm"
include "rexrd.mm"
include "adantr.mm"
include "xrltnle.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "itg2leub.mm"
include "syldan.mm"
include "mtbid.mm"
include "rexanali.mm"
include "sylibr.mm"
include "itg1cl.mm"
include "ltnle.mm"
include "syl2an.mm"
include "anbi2d.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "cmap.mm"
include "ovex.mm"
include "i1ff.mm"
include "reex.mm"
include "elmap.mm"
include "ssriv.mm"
include "ssexi.mm"
include "nnenom.mm"
include "breq1.mm"
include "fveq2.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "axcc4.mm"
include "simprl.mm"
include "simpl.mm"
include "ralimi.mm"
include "ad2antll.mm"
include "weq.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "supeq1i.mm"
include "wss.mm"
include "ffvelrn.mm"
include "eqid.mm"
include "fmptd.mm"
include "ad2antrl.mm"
include "frn.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "supxrcl.mm"
include "syl5eqelr.mm"
include "w3o.mm"
include "elxr.mm"
include "simplrl.mm"
include "arch.mm"
include "rexbidv.mm"
include "simplrr.mm"
include "posdifd.mm"
include "nnrecl.mm"
include "ltsub13.mm"
include "syl3anc.mm"
include "bitr4d.mm"
include "expr.mm"
include "rexr.mm"
include "syl2anr.mm"
include "rexnal.mm"
include "syl6bb.mm"
include "3imtr3d.mm"
include "con4d.mm"
include "pnfge.mm"
include "breqtrrd.mm"
include "a1d.mm"
include "c0.mm"
include "wne.mm"
include "1nn.mm"
include "ne0ii.mm"
include "r19.2z.mm"
include "mpan.mm"
include "mnflt.mm"
include "sylancr.mm"
include "simplr.mm"
include "mtbird.mm"
include "nrexdv.mm"
include "pm2.21d.mm"
include "syl5.mm"
include "3jaodan.mm"
include "sylan2b.mm"
include "adantll.mm"
include "xrltle.mm"
include "syl5eqssr.mm"
include "fvex.mm"
include "fvmpt.mm"
include "wfn.mm"
include "fnmpti.mm"
include "fnfvelrn.mm"
include "eqeltrrd.mm"
include "supxrub.mm"
include "xrletr.mm"
include "mpan2d.mm"
include "syld.mm"
include "adantld.mm"
include "ralimdva.mm"
include "impr.mm"
include "breq2.mm"
include "ralbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "syl6breqr.mm"
include "itg2ub.mm"
include "3expia.mm"
include "sylan2.mm"
include "anassrs.mm"
include "adantrd.mm"
include "breq1d.mm"
include "ralbiia.mm"
include "cbvralv.mm"
include "bitr4i.mm"
include "ffn.mm"
include "ralrn.mm"
include "3syl.mm"
include "supxrleub.mm"
include "xrletri3.mm"
include "adantrr.mm"
include "mpbir2and.mm"
include "3jca.mm"
include "ex.mm"
include "eximdv.mm"

theorem itg2seq
  let vg: setvar g
  let vn: setvar n
  let cF: class F
  let vf: setvar f
  let vm: setvar m
  let vx: setvar x
  let vz: setvar z

  disjoint g n
  disjoint F g
  disjoint F n
  disjoint f g
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f z
  disjoint F f
  disjoint g m
  disjoint g x
  disjoint g z
  disjoint m n
  disjoint m x
  disjoint m z
  disjoint F m
  disjoint n x
  disjoint n z
  disjoint x z
  disjoint F x
  disjoint F z
  assert |- ( F : RR --> ( 0 [,] +oo ) -> E. g ( g : NN --> dom S.1 /\ A. n e. NN ( g ` n ) oR <_ F /\ ( S.2 ` F ) = sup ( ran ( n e. NN |-> ( S.1 ` ( g ` n ) ) ) , RR* , < ) ) )

  proof
    cr
    cc0
    cpnf
    cicc
    co
    cF
    wf
    #
    cn
    citg1
    cdm
    #
    vg
    cv
    #
    wf
    #
    vn
    cv
    #
    @2
    cfv
    #
    cF
    cle
    cofr
    #
    wbr
    #
    cF
    citg2
    cfv
    #
    cpnf
    wceq
    #
    @4
    @8
    c1
    @4
    cdiv
    co
    #
    cmin
    co
    #
    cif
    #
    @5
    citg1
    cfv
    #
    clt
    wbr
    #
    wa
    #
    vn
    cn
    wral
    #
    wa
    #
    vg
    wex
    #
    @3
    @7
    vn
    cn
    wral
    #
    @8
    vn
    cn
    @13
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    wceq
    #
    w3a
    #
    vg
    wex
    @0
    vf
    cv
    #
    cF
    @6
    wbr
    #
    @12
    @25
    citg1
    cfv
    #
    clt
    wbr
    #
    wa
    #
    vf
    @1
    wrex
    #
    vn
    cn
    wral
    @18
    @0
    @30
    vn
    cn
    @0
    @4
    cn
    wcel
    #
    wa
    #
    @30
    @26
    @27
    @12
    cle
    wbr
    #
    wn
    #
    wa
    #
    vf
    @1
    wrex
    #
    @32
    @26
    @33
    wi
    vf
    @1
    wral
    #
    wn
    @36
    @32
    @8
    @12
    cle
    wbr
    #
    @37
    @32
    @12
    @8
    clt
    wbr
    #
    @38
    wn
    #
    @32
    @9
    @39
    @32
    @9
    wa
    #
    @4
    cpnf
    @12
    @8
    clt
    @41
    @4
    cr
    wcel
    #
    @4
    cpnf
    clt
    wbr
    @31
    @42
    @0
    @9
    @4
    nnre
    ad2antlr
    #
    @4
    ltpnf
    syl
    @9
    @12
    @4
    wceq
    #
    @32
    @9
    @4
    @11
    iftrue
    #
    adantl
    @32
    @9
    simpr
    3brtr4d
    @32
    @9
    wn
    #
    wa
    #
    @12
    @11
    @8
    clt
    @46
    @12
    @11
    wceq
    #
    @32
    @9
    @4
    @11
    iffalse
    #
    adantl
    @47
    @8
    @10
    @0
    @46
    @8
    cr
    wcel
    #
    @31
    @0
    @46
    @50
    @0
    @50
    cmnf
    @8
    clt
    wbr
    #
    @8
    cpnf
    clt
    wbr
    #
    wa
    #
    @52
    @46
    @0
    @8
    cxr
    wcel
    #
    @50
    @53
    wb
    cF
    itg2cl
    #
    @8
    xrrebnd
    syl
    @0
    @51
    @52
    @0
    cc0
    @8
    cle
    wbr
    #
    @51
    cF
    itg2ge0
    @0
    cmnf
    cc0
    clt
    wbr
    #
    @56
    @51
    mnflt0
    @0
    @54
    @57
    @56
    wa
    @51
    wi
    #
    @55
    cmnf
    cxr
    wcel
    #
    cc0
    cxr
    wcel
    @54
    @58
    mnfxr
    0xr
    cmnf
    cc0
    @8
    xrltletr
    mp3an12
    syl
    mpani
    mpd
    biantrurd
    @0
    @9
    @52
    @0
    @54
    @9
    @52
    wn
    wb
    @55
    @8
    nltpnft
    syl
    con2bid
    3bitr2rd
    biimpa
    #
    adantlr
    #
    @31
    @10
    crp
    wcel
    @0
    @46
    @31
    @4
    @4
    nnrp
    rpreccld
    ad2antlr
    ltsubrpd
    eqbrtrd
    pm2.61dan
    @32
    @12
    cxr
    wcel
    #
    @54
    @39
    @40
    wb
    @32
    @12
    @32
    @9
    @4
    @11
    cr
    @43
    @47
    @8
    @10
    @61
    @31
    @10
    cr
    wcel
    #
    @0
    @46
    @4
    nnrecre
    #
    ad2antlr
    resubcld
    ifclda
    #
    rexrd
    #
    @0
    @54
    @31
    @55
    adantr
    @12
    @8
    xrltnle
    syl2anc
    mpbid
    @0
    @31
    @62
    @38
    @37
    wb
    @66
    @12
    vf
    cF
    itg2leub
    syldan
    mtbid
    @26
    @33
    vf
    @1
    rexanali
    sylibr
    @32
    @29
    @35
    vf
    @1
    @32
    @25
    @1
    wcel
    #
    wa
    @28
    @34
    @26
    @32
    @12
    cr
    wcel
    #
    @27
    cr
    wcel
    @28
    @34
    wb
    @67
    @65
    @25
    itg1cl
    @12
    @27
    ltnle
    syl2an
    anbi2d
    rexbidva
    mpbird
    ralrimiva
    @29
    @15
    vf
    @1
    vg
    vn
    cn
    @1
    cr
    cr
    cmap
    co
    #
    cr
    cr
    cmap
    ovex
    vx
    @1
    @69
    vx
    cv
    #
    @1
    wcel
    cr
    cr
    @70
    wf
    @70
    @69
    wcel
    @70
    i1ff
    cr
    cr
    @70
    reex
    reex
    elmap
    sylibr
    ssriv
    ssexi
    nnenom
    @25
    @5
    wceq
    #
    @26
    @7
    @28
    @14
    @25
    @5
    cF
    @6
    breq1
    @71
    @27
    @13
    @12
    clt
    @25
    @5
    citg1
    fveq2
    breq2d
    anbi12d
    axcc4
    syl
    @0
    @17
    @24
    vg
    @0
    @17
    @24
    @0
    @17
    wa
    #
    @3
    @19
    @23
    @0
    @3
    @16
    simprl
    @16
    @19
    @0
    @3
    @15
    @7
    vn
    cn
    @7
    @14
    simpl
    ralimi
    ad2antll
    @72
    @23
    @8
    @22
    cle
    wbr
    #
    @22
    @8
    cle
    wbr
    #
    @72
    @8
    vm
    cn
    vm
    cv
    #
    @2
    cfv
    #
    citg1
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    @22
    cle
    @72
    @80
    cxr
    wcel
    #
    @12
    @70
    cle
    wbr
    #
    vn
    cn
    wral
    #
    @8
    @70
    cle
    wbr
    #
    wi
    #
    vx
    cxr
    wral
    #
    @12
    @80
    cle
    wbr
    #
    vn
    cn
    wral
    #
    @8
    @80
    cle
    wbr
    #
    @72
    @80
    @22
    cxr
    cxr
    @21
    @79
    clt
    @20
    @78
    vn
    vm
    cn
    @13
    @77
    vn
    vm
    weq
    #
    @5
    @76
    citg1
    @4
    @75
    @2
    fveq2
    fveq2d
    #
    cbvmptv
    rneqi
    #
    supeq1i
    #
    @72
    @21
    cxr
    wss
    #
    @22
    cxr
    wcel
    #
    @72
    @21
    cr
    cxr
    @72
    cn
    cr
    @20
    wf
    #
    @21
    cr
    wss
    #
    @3
    @96
    @0
    @16
    @3
    vn
    cn
    @13
    cr
    @20
    @3
    @31
    wa
    #
    @5
    @1
    wcel
    #
    @13
    cr
    wcel
    #
    cn
    @1
    @4
    @2
    ffvelrn
    #
    @5
    itg1cl
    syl
    #
    @20
    eqid
    #
    fmptd
    #
    ad2antrl
    #
    cn
    cr
    @20
    frn
    #
    syl
    ressxr
    syl6ss
    #
    @21
    supxrcl
    #
    syl
    syl5eqelr
    @0
    @86
    @17
    @0
    @85
    vx
    cxr
    @70
    cxr
    wcel
    #
    @0
    @70
    cr
    wcel
    #
    @70
    cpnf
    wceq
    #
    @70
    cmnf
    wceq
    #
    w3o
    @85
    @70
    elxr
    @0
    @110
    @85
    @111
    @112
    @0
    @110
    wa
    #
    @84
    @83
    @113
    @70
    @8
    clt
    wbr
    #
    @70
    @12
    clt
    wbr
    #
    vn
    cn
    wrex
    #
    @84
    wn
    #
    @83
    wn
    #
    @0
    @110
    @114
    @116
    @0
    @110
    @114
    wa
    #
    wa
    #
    @9
    @116
    @120
    @9
    wa
    #
    @116
    @70
    @4
    clt
    wbr
    #
    vn
    cn
    wrex
    #
    @121
    @110
    @123
    @0
    @110
    @114
    @9
    simplrl
    @70
    vn
    arch
    syl
    @121
    @115
    @122
    vn
    cn
    @121
    @12
    @4
    @70
    clt
    @9
    @44
    @120
    @45
    adantl
    breq2d
    rexbidv
    mpbird
    @120
    @46
    wa
    #
    @10
    @8
    @70
    cmin
    co
    #
    clt
    wbr
    #
    vn
    cn
    wrex
    #
    @116
    @124
    @125
    cr
    wcel
    cc0
    @125
    clt
    wbr
    #
    @127
    @124
    @8
    @70
    @0
    @46
    @50
    @119
    @60
    adantlr
    #
    @0
    @110
    @114
    @46
    simplrl
    #
    resubcld
    @124
    @114
    @128
    @0
    @110
    @114
    @46
    simplrr
    @124
    @70
    @8
    @130
    @129
    posdifd
    mpbid
    @125
    vn
    nnrecl
    syl2anc
    @124
    @126
    @115
    vn
    cn
    @124
    @31
    wa
    #
    @126
    @70
    @11
    clt
    wbr
    #
    @115
    @131
    @63
    @50
    @110
    @126
    @132
    wb
    @31
    @63
    @124
    @64
    adantl
    @124
    @50
    @31
    @129
    adantr
    @124
    @110
    @31
    @130
    adantr
    @10
    @8
    @70
    ltsub13
    syl3anc
    @131
    @12
    @11
    @70
    clt
    @46
    @48
    @120
    @31
    @49
    ad2antlr
    breq2d
    bitr4d
    rexbidva
    mpbid
    pm2.61dan
    expr
    @110
    @109
    @54
    @114
    @117
    wb
    @0
    @70
    rexr
    #
    @55
    @70
    @8
    xrltnle
    syl2anr
    @113
    @116
    @82
    wn
    #
    vn
    cn
    wrex
    @118
    @113
    @115
    @134
    vn
    cn
    @113
    @31
    wa
    @109
    @62
    @115
    @134
    wb
    @110
    @109
    @0
    @31
    @133
    ad2antlr
    @0
    @31
    @62
    @110
    @66
    adantlr
    @70
    @12
    xrltnle
    syl2anc
    rexbidva
    @82
    vn
    cn
    rexnal
    syl6bb
    3imtr3d
    con4d
    @0
    @111
    wa
    #
    @84
    @83
    @135
    @8
    cpnf
    @70
    cle
    @135
    @54
    @8
    cpnf
    cle
    wbr
    @0
    @54
    @111
    @55
    adantr
    @8
    pnfge
    syl
    @0
    @111
    simpr
    breqtrrd
    a1d
    @83
    @82
    vn
    cn
    wrex
    #
    @0
    @112
    wa
    #
    @84
    cn
    c0
    wne
    @83
    @136
    c1
    cn
    1nn
    ne0ii
    @82
    vn
    cn
    r19.2z
    mpan
    @137
    @136
    @84
    @137
    @82
    vn
    cn
    @137
    @31
    wa
    #
    @82
    @12
    cmnf
    cle
    wbr
    #
    @138
    @68
    @139
    wn
    #
    @0
    @31
    @68
    @112
    @65
    adantlr
    @68
    cmnf
    @12
    clt
    wbr
    #
    @140
    @12
    mnflt
    @68
    @59
    @62
    @141
    @140
    wb
    mnfxr
    @12
    rexr
    cmnf
    @12
    xrltnle
    sylancr
    mpbid
    syl
    @138
    @70
    cmnf
    @12
    cle
    @0
    @112
    @31
    simplr
    breq2d
    mtbird
    nrexdv
    pm2.21d
    syl5
    3jaodan
    sylan2b
    ralrimiva
    adantr
    @0
    @3
    @16
    @88
    @0
    @3
    wa
    #
    @15
    @87
    vn
    cn
    @142
    @31
    wa
    #
    @14
    @87
    @7
    @143
    @14
    @12
    @13
    cle
    wbr
    #
    @87
    @143
    @62
    @13
    cxr
    wcel
    #
    @14
    @144
    wi
    @0
    @31
    @62
    @3
    @66
    adantlr
    #
    @143
    @13
    @3
    @31
    @100
    @0
    @102
    adantll
    rexrd
    #
    @12
    @13
    xrltle
    syl2anc
    @143
    @144
    @13
    @80
    cle
    wbr
    #
    @87
    @143
    @79
    cxr
    wss
    @13
    @79
    wcel
    #
    @148
    @143
    @79
    @21
    cxr
    @92
    @142
    @94
    @31
    @142
    @21
    cr
    cxr
    @142
    @96
    @97
    @3
    @96
    @0
    @104
    adantl
    @106
    syl
    ressxr
    syl6ss
    #
    adantr
    #
    syl5eqssr
    @31
    @149
    @142
    @31
    @4
    @78
    cfv
    #
    @13
    @79
    vm
    @4
    @77
    @13
    cn
    @78
    vm
    vn
    weq
    @76
    @5
    citg1
    @75
    @4
    @2
    fveq2
    fveq2d
    @78
    eqid
    #
    @5
    citg1
    fvex
    fvmpt
    @78
    cn
    wfn
    @31
    @152
    @79
    wcel
    vm
    cn
    @77
    @78
    @76
    citg1
    fvex
    #
    @153
    fnmpti
    cn
    @4
    @78
    fnfvelrn
    mpan
    eqeltrrd
    adantl
    @79
    @13
    supxrub
    syl2anc
    @143
    @62
    @145
    @81
    @144
    @148
    wa
    @87
    wi
    @146
    @147
    @143
    @80
    @22
    cxr
    @93
    @143
    @94
    @95
    @151
    @108
    syl
    syl5eqelr
    @12
    @13
    @80
    xrletr
    syl3anc
    mpan2d
    syld
    adantld
    ralimdva
    impr
    @85
    @88
    @89
    wi
    vx
    @80
    cxr
    @70
    @80
    wceq
    #
    @83
    @88
    @84
    @89
    @155
    @82
    @87
    vn
    cn
    @70
    @80
    @12
    cle
    breq2
    ralbidv
    @70
    @80
    @8
    cle
    breq2
    imbi12d
    rspcv
    syl3c
    @93
    syl6breqr
    @72
    @74
    vz
    cv
    #
    @8
    cle
    wbr
    #
    vz
    @21
    wral
    #
    @72
    @158
    @75
    @20
    cfv
    #
    @8
    cle
    wbr
    #
    vm
    cn
    wral
    #
    @72
    @13
    @8
    cle
    wbr
    #
    vn
    cn
    wral
    #
    @161
    @0
    @3
    @16
    @163
    @142
    @15
    @162
    vn
    cn
    @143
    @7
    @162
    @14
    @0
    @3
    @31
    @7
    @162
    wi
    #
    @98
    @0
    @99
    @164
    @101
    @0
    @99
    @7
    @162
    cF
    @5
    itg2ub
    3expia
    sylan2
    anassrs
    adantrd
    ralimdva
    impr
    @161
    @77
    @8
    cle
    wbr
    #
    vm
    cn
    wral
    @163
    @160
    @165
    vm
    cn
    @75
    cn
    wcel
    @159
    @77
    @8
    cle
    vn
    @75
    @13
    @77
    cn
    @20
    @91
    @103
    @154
    fvmpt
    breq1d
    ralbiia
    @162
    @165
    vn
    vm
    cn
    @90
    @13
    @77
    @8
    cle
    @91
    breq1d
    cbvralv
    bitr4i
    sylibr
    @72
    @96
    @20
    cn
    wfn
    @158
    @161
    wb
    @105
    cn
    cr
    @20
    ffn
    @157
    @160
    vz
    vm
    cn
    @20
    @156
    @159
    @8
    cle
    breq1
    ralrn
    3syl
    mpbird
    @72
    @94
    @54
    @74
    @158
    wb
    @107
    @0
    @54
    @17
    @55
    adantr
    vz
    @21
    @8
    supxrleub
    syl2anc
    mpbird
    @0
    @3
    @23
    @73
    @74
    wa
    wb
    #
    @16
    @142
    @54
    @95
    @166
    @0
    @54
    @3
    @55
    adantr
    @142
    @94
    @95
    @150
    @108
    syl
    @8
    @22
    xrletri3
    syl2anc
    adantrr
    mpbir2and
    3jca
    ex
    eximdv
    mpd
end
