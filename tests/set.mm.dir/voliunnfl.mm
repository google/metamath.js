include "cn.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cuni.mm"
include "cr.mm"
include "wss.mm"
include "wne.mm"
include "cc0.mm"
include "cvol.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "c0.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "covol.mm"
include "cdm.mm"
include "wcel.mm"
include "0mbl.mm"
include "mblvol.mm"
include "ax-mp.mm"
include "ovol0.mm"
include "eqtri.mm"
include "syl6req.mm"
include "a1d.mm"
include "wfo.mm"
include "wex.mm"
include "csdm.mm"
include "cvv.mm"
include "wb.mm"
include "reldom.mm"
include "brrelexi.mm"
include "0sdomg.mm"
include "syl.mm"
include "biimparc.mm"
include "fodomr.mm"
include "sylancom.mm"
include "unissb.mm"
include "anbi1i.mm"
include "r19.26.mm"
include "bitr4i.mm"
include "ovolctb2.mm"
include "ex.mm"
include "imdistani.mm"
include "ralimi.mm"
include "sylbi.mm"
include "ancoms.mm"
include "cima.mm"
include "foima.mm"
include "raleqdv.mm"
include "wfn.mm"
include "fofn.mm"
include "ssid.mm"
include "sseq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "ralima.mm"
include "sylancl.mm"
include "bitr3d.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "ciun.mm"
include "cdif.mm"
include "caddc.mm"
include "cmpt.mm"
include "cseq.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wdisj.mm"
include "difss.mm"
include "ovolssnul.mm"
include "mp3an1.mm"
include "ssdifss.mm"
include "nulmbl.mm"
include "biimpar.mm"
include "0re.mm"
include "syl6eqel.mm"
include "expcom.mm"
include "ancld.mm"
include "adantl.mm"
include "mpd.mm"
include "sylan.mm"
include "syldan.mm"
include "weq.mm"
include "oveq2.mm"
include "iuneq1d.mm"
include "difeq12d.mm"
include "eqid.mm"
include "fvex.mm"
include "difexg.mm"
include "fvmpt.mm"
include "eleq1d.mm"
include "ralbiia.mm"
include "cbvralv.mm"
include "bitri.mm"
include "sylibr.mm"
include "iundisj2.mm"
include "disjeq2.mm"
include "mprg.mm"
include "mpbir.mm"
include "nnex.mm"
include "mptex.mm"
include "fveq1.mm"
include "ralbidv.mm"
include "adantr.mm"
include "disjeq2dv.mm"
include "iuneq2d.mm"
include "seqeq3.mm"
include "rneqi.mm"
include "supeq1i.mm"
include "mpteq2dv.mm"
include "seqeq3d.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "syl5eq.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "vtocl.mm"
include "iuneq2i.mm"
include "fveq2i.mm"
include "mpteq2ia.mm"
include "3eqtr3g.mm"
include "iundisj.mm"
include "wfun.mm"
include "fofun.mm"
include "funiunfv.mm"
include "syl5eqr.mm"
include "unieqd.mm"
include "eqtrd.mm"
include "sseq1d.mm"
include "rspccva.mm"
include "jca.mm"
include "3syl.mm"
include "mpteq2dva.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cc.mm"
include "0cn.mm"
include "ser1const.mm"
include "mpan.mm"
include "nncn.mm"
include "mul01d.mm"
include "fconstmpt.mm"
include "cuz.mm"
include "cz.mm"
include "1z.mm"
include "seqfn.mm"
include "nnuz.mm"
include "fneq2i.mm"
include "dffn5.mm"
include "bitr3i.mm"
include "mpbi.mm"
include "eqtr3i.mm"
include "3eqtr4i.mm"
include "1nn.mm"
include "ne0i.mm"
include "rnxp.mm"
include "mp2b.mm"
include "wor.mm"
include "xrltso.mm"
include "0xr.mm"
include "supsn.mm"
include "mp2an.mm"
include "3eqtr3rd.mm"
include "sylbid.mm"
include "syl5.mm"
include "exlimiv.mm"
include "expimpd.mm"
include "pm2.61ine.mm"
include "cpnf.mm"
include "renepnf.mm"
include "mp1i.mm"
include "rembl.mm"
include "ovolre.mm"
include "neeqtrrd.mm"
include "necon2i.mm"
include "expr.mm"
include "eqimss.mm"
include "necon3bi.mm"
include "pm2.61d1.mm"

theorem voliunnfl
  let vx: setvar x
  let cA: class A
  let cS: class S
  let vf: setvar f
  let vn: setvar n
  let cG: class G
  let vg: setvar g
  let vm: setvar m
  let vl: setvar l
  assume voliunnfl.1: |- S = seq 1 ( + , G )
  assume voliunnfl.2: |- G = ( n e. NN |-> ( vol ` ( f ` n ) ) )
  assume voliunnfl.3: |- ( ( A. n e. NN ( ( f ` n ) e. dom vol /\ ( vol ` ( f ` n ) ) e. RR ) /\ Disj_ n e. NN ( f ` n ) ) -> ( vol ` U_ n e. NN ( f ` n ) ) = sup ( ran S , RR* , < ) )

  disjoint f n
  disjoint f x
  disjoint A f
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint f g
  disjoint f m
  disjoint f l
  disjoint g m
  disjoint g n
  disjoint g l
  disjoint g x
  disjoint A g
  disjoint m n
  disjoint l m
  disjoint m x
  disjoint A m
  disjoint l n
  disjoint l x
  disjoint A l
  assert |- ( ( A ~<_ NN /\ A. x e. A x ~<_ NN ) -> U. A =/= RR )

  proof
    cA
    cn
    cdom
    wbr
    #
    vx
    cv
    #
    cn
    cdom
    wbr
    #
    vx
    cA
    wral
    #
    wa
    cA
    cuni
    #
    cr
    wss
    #
    @4
    cr
    wne
    #
    @0
    @3
    @5
    @6
    @0
    @3
    @5
    wa
    #
    wa
    #
    cc0
    @4
    cvol
    cfv
    #
    wceq
    #
    @6
    @8
    @10
    wi
    cA
    c0
    cA
    c0
    wceq
    #
    @10
    @8
    @11
    @9
    c0
    cvol
    cfv
    #
    cc0
    @11
    @4
    c0
    cvol
    @11
    @4
    c0
    cuni
    c0
    cA
    c0
    unieq
    uni0
    syl6eq
    fveq2d
    @12
    c0
    covol
    cfv
    #
    cc0
    c0
    cvol
    cdm
    #
    wcel
    @12
    @13
    wceq
    0mbl
    c0
    mblvol
    ax-mp
    ovol0
    eqtri
    syl6req
    a1d
    cA
    c0
    wne
    #
    @0
    @7
    @10
    @15
    @0
    wa
    cn
    cA
    vg
    cv
    #
    wfo
    #
    vg
    wex
    #
    @7
    @10
    wi
    #
    @15
    @0
    c0
    cA
    csdm
    wbr
    #
    @18
    @0
    @20
    @15
    @0
    cA
    cvv
    wcel
    @20
    @15
    wb
    cA
    cn
    cdom
    reldom
    brrelexi
    cA
    cvv
    0sdomg
    syl
    biimparc
    cn
    cA
    vg
    fodomr
    sylancom
    @17
    @19
    vg
    @7
    @1
    cr
    wss
    #
    @1
    covol
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vx
    cA
    wral
    #
    @17
    @10
    @5
    @3
    @25
    @5
    @3
    wa
    #
    @21
    @2
    wa
    #
    vx
    cA
    wral
    #
    @25
    @26
    @21
    vx
    cA
    wral
    #
    @3
    wa
    @28
    @5
    @29
    @3
    vx
    cA
    cr
    unissb
    anbi1i
    @21
    @2
    vx
    cA
    r19.26
    bitr4i
    @27
    @24
    vx
    cA
    @21
    @2
    @23
    @21
    @2
    @23
    @1
    ovolctb2
    ex
    imdistani
    ralimi
    sylbi
    ancoms
    @17
    @25
    vm
    cv
    #
    @16
    cfv
    #
    cr
    wss
    #
    @31
    covol
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vm
    cn
    wral
    #
    @10
    @17
    @24
    vx
    @16
    cn
    cima
    #
    wral
    #
    @25
    @36
    @17
    @24
    vx
    @37
    cA
    cn
    cA
    @16
    foima
    #
    raleqdv
    @17
    @16
    cn
    wfn
    cn
    cn
    wss
    @38
    @36
    wb
    cn
    cA
    @16
    fofn
    cn
    ssid
    @24
    @35
    vx
    vm
    cn
    cn
    @16
    @1
    @31
    wceq
    #
    @21
    @32
    @23
    @34
    @1
    @31
    cr
    sseq1
    @40
    @22
    @33
    cc0
    @1
    @31
    covol
    fveq2
    eqeq1d
    anbi12d
    ralima
    sylancl
    bitr3d
    @17
    @36
    @10
    @17
    @36
    wa
    vn
    cn
    vn
    cv
    #
    @16
    cfv
    #
    vl
    c1
    @41
    cfzo
    co
    #
    vl
    cv
    #
    @16
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
    vn
    cn
    @47
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
    @9
    cc0
    @36
    @49
    @54
    wceq
    #
    @17
    @36
    @41
    vm
    cn
    @31
    vl
    c1
    @30
    cfzo
    co
    #
    @45
    ciun
    #
    cdif
    #
    cmpt
    #
    cfv
    #
    @14
    wcel
    #
    @60
    cvol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    vn
    cn
    wral
    #
    vn
    cn
    @60
    wdisj
    #
    @55
    @36
    @58
    @14
    wcel
    #
    @58
    cvol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    vm
    cn
    wral
    #
    @65
    @35
    @70
    vm
    cn
    @32
    @34
    @58
    covol
    cfv
    #
    cc0
    wceq
    #
    @70
    @58
    @31
    wss
    @32
    @34
    @73
    @31
    @57
    difss
    @58
    @31
    ovolssnul
    mp3an1
    @32
    @58
    cr
    wss
    #
    @73
    @70
    @31
    cr
    @57
    ssdifss
    @74
    @73
    wa
    @67
    @70
    @58
    nulmbl
    @73
    @67
    @70
    wi
    @74
    @73
    @67
    @69
    @67
    @73
    @69
    @67
    @73
    wa
    @68
    cc0
    cr
    @67
    @68
    cc0
    wceq
    @73
    @67
    @68
    @72
    cc0
    @58
    mblvol
    eqeq1d
    biimpar
    0re
    syl6eqel
    expcom
    ancld
    adantl
    mpd
    sylan
    syldan
    ralimi
    @65
    @47
    @14
    wcel
    #
    @50
    cr
    wcel
    #
    wa
    #
    vn
    cn
    wral
    @71
    @64
    @77
    vn
    cn
    @41
    cn
    wcel
    #
    @61
    @75
    @63
    @76
    @78
    @60
    @47
    @14
    vm
    @41
    @58
    @47
    cn
    @59
    vm
    vn
    weq
    #
    @31
    @42
    @57
    @46
    @30
    @41
    @16
    fveq2
    #
    @79
    vl
    @56
    @43
    @45
    @30
    @41
    c1
    cfzo
    oveq2
    iuneq1d
    difeq12d
    @59
    eqid
    @42
    cvv
    wcel
    @47
    cvv
    wcel
    @41
    @16
    fvex
    @42
    @46
    cvv
    difexg
    ax-mp
    fvmpt
    #
    eleq1d
    @78
    @62
    @50
    cr
    @78
    @60
    @47
    cvol
    @81
    fveq2d
    #
    eleq1d
    anbi12d
    ralbiia
    @77
    @70
    vn
    vm
    cn
    vn
    vm
    weq
    #
    @75
    @67
    @76
    @69
    @83
    @47
    @58
    @14
    @83
    @42
    @31
    @46
    @57
    @41
    @30
    @16
    fveq2
    @83
    vl
    @43
    @56
    @45
    @41
    @30
    c1
    cfzo
    oveq2
    iuneq1d
    difeq12d
    #
    eleq1d
    @83
    @50
    @68
    cr
    @83
    @47
    @58
    cvol
    @84
    fveq2d
    eleq1d
    anbi12d
    cbvralv
    bitri
    sylibr
    @66
    vn
    cn
    @47
    wdisj
    #
    @42
    @45
    vl
    vn
    @41
    @44
    @16
    fveq2
    #
    iundisj2
    @60
    @47
    wceq
    @66
    @85
    wb
    vn
    cn
    vn
    cn
    @60
    @47
    disjeq2
    @81
    mprg
    mpbir
    @65
    @66
    wa
    #
    vn
    cn
    @60
    ciun
    #
    cvol
    cfv
    #
    caddc
    vn
    cn
    @62
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
    @49
    @54
    @41
    vf
    cv
    #
    cfv
    #
    @14
    wcel
    #
    @95
    cvol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    vn
    cn
    wral
    #
    vn
    cn
    @95
    wdisj
    #
    wa
    #
    vn
    cn
    @95
    ciun
    #
    cvol
    cfv
    #
    cS
    crn
    #
    cxr
    clt
    csup
    #
    wceq
    #
    wi
    @87
    @89
    @93
    wceq
    #
    wi
    vf
    @59
    vm
    cn
    @58
    nnex
    mptex
    @94
    @59
    wceq
    #
    @102
    @87
    @107
    @108
    @109
    @100
    @65
    @101
    @66
    @109
    @99
    @64
    vn
    cn
    @109
    @96
    @61
    @98
    @63
    @109
    @95
    @60
    @14
    @41
    @94
    @59
    fveq1
    #
    eleq1d
    @109
    @97
    @62
    cr
    @109
    @95
    @60
    cvol
    @110
    fveq2d
    #
    eleq1d
    anbi12d
    ralbidv
    @109
    vn
    cn
    @95
    @60
    @109
    @95
    @60
    wceq
    @78
    @110
    adantr
    disjeq2dv
    anbi12d
    @109
    @104
    @89
    @106
    @93
    @109
    @103
    @88
    cvol
    @109
    vn
    cn
    @95
    @60
    @110
    iuneq2d
    fveq2d
    @109
    @106
    caddc
    vn
    cn
    @97
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
    @93
    cxr
    @105
    @114
    clt
    cS
    @113
    cS
    caddc
    cG
    c1
    cseq
    #
    @113
    voliunnfl.1
    cG
    @112
    wceq
    @115
    @113
    wceq
    voliunnfl.2
    caddc
    cG
    @112
    c1
    seqeq3
    ax-mp
    eqtri
    rneqi
    supeq1i
    @109
    cxr
    @114
    @92
    clt
    @109
    @113
    @91
    @109
    @112
    @90
    caddc
    c1
    @109
    vn
    cn
    @97
    @62
    @111
    mpteq2dv
    seqeq3d
    rneqd
    supeq1d
    syl5eq
    eqeq12d
    imbi12d
    voliunnfl.3
    vtocl
    @88
    @48
    cvol
    vn
    cn
    @60
    @47
    @81
    iuneq2i
    fveq2i
    cxr
    @92
    @53
    clt
    @91
    @52
    @90
    @51
    wceq
    @91
    @52
    wceq
    vn
    cn
    @62
    @50
    @82
    mpteq2ia
    caddc
    @90
    @51
    c1
    seqeq3
    ax-mp
    rneqi
    supeq1i
    3eqtr3g
    sylancl
    adantl
    @17
    @49
    @9
    wceq
    @36
    @17
    @48
    @4
    cvol
    @17
    @48
    @37
    cuni
    #
    @4
    @17
    @48
    vn
    cn
    @42
    ciun
    #
    @116
    @42
    @45
    vl
    vn
    @86
    iundisj
    @17
    @16
    wfun
    @117
    @116
    wceq
    cn
    cA
    @16
    fofun
    vn
    cn
    @16
    funiunfv
    syl
    syl5eqr
    @17
    @37
    cA
    @39
    unieqd
    eqtrd
    fveq2d
    adantr
    @36
    @54
    cc0
    wceq
    @17
    @36
    @54
    caddc
    vn
    cn
    cc0
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
    cc0
    @36
    cxr
    @53
    @120
    clt
    @36
    @52
    @119
    @36
    @51
    @118
    caddc
    c1
    @36
    vn
    cn
    @50
    cc0
    @36
    @78
    wa
    @42
    cr
    wss
    #
    @42
    covol
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    @50
    cc0
    wceq
    @35
    @125
    vm
    @41
    cn
    @79
    @32
    @122
    @34
    @124
    @79
    @31
    @42
    cr
    @80
    sseq1d
    @79
    @33
    @123
    cc0
    @79
    @31
    @42
    covol
    @80
    fveq2d
    eqeq1d
    anbi12d
    rspccva
    @125
    @50
    @47
    covol
    cfv
    #
    cc0
    @125
    @47
    cr
    wss
    #
    @126
    cc0
    wceq
    #
    wa
    @75
    @50
    @126
    wceq
    @125
    @127
    @128
    @122
    @127
    @124
    @42
    cr
    @46
    ssdifss
    adantr
    @47
    @42
    wss
    @122
    @124
    @128
    @42
    @46
    difss
    @47
    @42
    ovolssnul
    mp3an1
    #
    jca
    @47
    nulmbl
    @47
    mblvol
    3syl
    @129
    eqtrd
    syl
    mpteq2dva
    seqeq3d
    rneqd
    supeq1d
    @121
    cc0
    csn
    #
    cxr
    clt
    csup
    #
    cc0
    cxr
    @120
    @130
    clt
    @120
    cn
    @130
    cxp
    #
    crn
    #
    @130
    @119
    @132
    vm
    cn
    @30
    caddc
    @132
    c1
    cseq
    #
    cfv
    #
    cmpt
    #
    vm
    cn
    cc0
    cmpt
    @119
    @132
    vm
    cn
    @135
    cc0
    @30
    cn
    wcel
    #
    @135
    @30
    cc0
    cmul
    co
    #
    cc0
    cc0
    cc
    wcel
    @137
    @135
    @138
    wceq
    0cn
    cc0
    @30
    ser1const
    mpan
    @137
    @30
    @30
    nncn
    mul01d
    eqtrd
    mpteq2ia
    @134
    @119
    @136
    @132
    @118
    wceq
    @134
    @119
    wceq
    vn
    cn
    cc0
    fconstmpt
    caddc
    @132
    @118
    c1
    seqeq3
    ax-mp
    @134
    c1
    cuz
    cfv
    #
    wfn
    #
    @134
    @136
    wceq
    #
    c1
    cz
    wcel
    @140
    1z
    caddc
    @132
    c1
    seqfn
    ax-mp
    @140
    @134
    cn
    wfn
    @141
    cn
    @139
    @134
    nnuz
    fneq2i
    vm
    cn
    @134
    dffn5
    bitr3i
    mpbi
    eqtr3i
    vm
    cn
    cc0
    fconstmpt
    3eqtr4i
    rneqi
    c1
    cn
    wcel
    cn
    c0
    wne
    @133
    @130
    wceq
    1nn
    cn
    c1
    ne0i
    cn
    @130
    rnxp
    mp2b
    eqtri
    supeq1i
    cxr
    clt
    wor
    cc0
    cxr
    wcel
    @131
    cc0
    wceq
    xrltso
    0xr
    cxr
    cc0
    clt
    supsn
    mp2an
    eqtri
    syl6eq
    adantl
    3eqtr3rd
    ex
    sylbid
    syl5
    exlimiv
    syl
    expimpd
    pm2.61ine
    @4
    cr
    cc0
    @9
    @4
    cr
    wceq
    #
    cc0
    cpnf
    @9
    cc0
    cr
    wcel
    cc0
    cpnf
    wne
    @142
    0re
    cc0
    renepnf
    mp1i
    @142
    @9
    cr
    cvol
    cfv
    #
    cpnf
    @4
    cr
    cvol
    fveq2
    @143
    cr
    covol
    cfv
    #
    cpnf
    cr
    @14
    wcel
    @143
    @144
    wceq
    rembl
    cr
    mblvol
    ax-mp
    ovolre
    eqtri
    syl6eq
    neeqtrrd
    necon2i
    syl
    expr
    @5
    @4
    cr
    @4
    cr
    eqimss
    necon3bi
    pm2.61d1
end
