include "clmod.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "clspn.mm"
include "wn.mm"
include "cbs.mm"
include "wral.mm"
include "cof.mm"
include "cgsu.mm"
include "wceq.mm"
include "cxp.mm"
include "wi.mm"
include "clindf.mm"
include "wbr.mm"
include "wa.mm"
include "cminusg.mm"
include "raldifsni.mm"
include "cfsupp.mm"
include "cres.mm"
include "cmap.mm"
include "crab.mm"
include "cop.mm"
include "cun.mm"
include "wb.mm"
include "cplusg.mm"
include "simpll1.mm"
include "simprll.mm"
include "ffvelrn.mm"
include "3ad2antl3.mm"
include "adantr.mm"
include "eqid.mm"
include "lmodvsinv.mm"
include "syl3anc.mm"
include "eqeq1d.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "syl.mm"
include "lmodvscl.mm"
include "cvv.mm"
include "ccmn.mm"
include "lmodcmn.mm"
include "simpll2.mm"
include "difexg.mm"
include "simprlr.mm"
include "elmapi.mm"
include "wss.mm"
include "simpll3.mm"
include "difss.mm"
include "fssres.mm"
include "sylancl.mm"
include "lcomf.mm"
include "simprr.mm"
include "lcomfsupp.mm"
include "gsumcl.mm"
include "grpinvid2.mm"
include "simplr.mm"
include "fsnunf2.mm"
include "wfun.mm"
include "cdm.mm"
include "wnel.mm"
include "simpr.mm"
include "simpl.mm"
include "anim12i.mm"
include "elmapfun.mm"
include "fdm.mm"
include "neldifsnd.mm"
include "df-nel.mm"
include "eleq2.mm"
include "notbid.mm"
include "syl5bb.mm"
include "mpbird.mm"
include "jca.mm"
include "adantl.mm"
include "funsnfsupp.mm"
include "bicomd.mm"
include "biimpd.mm"
include "impr.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "a1i.mm"
include "difsnid.mm"
include "eqcomd.mm"
include "gsumsplit.mm"
include "vex.mm"
include "snex.mm"
include "unex.mm"
include "simpl3.mm"
include "simpl2.mm"
include "fex.mm"
include "syl2anc.mm"
include "offres.mm"
include "sylancr.mm"
include "wfn.mm"
include "ffn.mm"
include "neldifsn.mm"
include "fsnunres.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "cmpt.mm"
include "fnressn.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "fndm.mm"
include "eleq2d.mm"
include "mtbiri.mm"
include "fsnunfv.mm"
include "mp3an12.mm"
include "3syl.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "ovex.mm"
include "fmptsn.mm"
include "mp2an.mm"
include "3eqtrd.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "eqidd.mm"
include "gsumsn.mm"
include "oveq12d.mm"
include "eqtr2d.mm"
include "3bitrd.mm"
include "imbi12d.mm"
include "anassrs.mm"
include "pm5.74da.mm"
include "impexp.mm"
include "imbi1d.mm"
include "3bitr4d.mm"
include "2ralbidva.mm"
include "breq1.mm"
include "oveq1.mm"
include "fveq1.mm"
include "ralxpmap.mm"
include "bitr4d.mm"
include "ralrab.mm"
include "syl6bbr.mm"
include "wrex.mm"
include "resima.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "eleq2i.mm"
include "simpl1.mm"
include "3ad2ant2.mm"
include "ellspd.mm"
include "r19.23v.mm"
include "ralbidv.mm"
include "cfrlm.mm"
include "csca.mm"
include "fvex.mm"
include "eqeltri.mm"
include "frlmbas.mm"
include "mpan.mm"
include "syl6reqr.mm"
include "raleqdv.mm"
include "lmodfgrp.mm"
include "grpinvnzcl.mm"
include "sylan.mm"
include "eldifi.mm"
include "grpinvinv.mm"
include "syl2an.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "eleq1d.mm"
include "ralxfrd.mm"
include "3ad2ant1.mm"
include "c0g.mm"
include "fvconst2.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "islindf2.mm"
include "frlmbasf.mm"
include "3ad2antl2.mm"
include "fnconstg.mm"
include "ax-mp.mm"
include "eqfnfv.mm"
include "r19.21v.mm"
include "ralbii.mm"
include "ralcom.mm"
include "bitr3i.mm"
include "syl6bb.mm"

theorem islindf4
  let vx: setvar x
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cI: class I
  let cL: class L
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  let vy: setvar y
  let vz: setvar z
  assume islindf4.b: |- B = ( Base ` W )
  assume islindf4.r: |- R = ( Scalar ` W )
  assume islindf4.t: |- .x. = ( .s ` W )
  assume islindf4.z: |- .0. = ( 0g ` W )
  assume islindf4.y: |- Y = ( 0g ` R )
  assume islindf4.l: |- L = ( Base ` ( R freeLMod I ) )

  disjoint B x
  disjoint F x
  disjoint I x
  disjoint L x
  disjoint R x
  disjoint .x. x
  disjoint W x
  disjoint X x
  disjoint Y x
  disjoint .0. x
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint B y
  disjoint x y
  disjoint F j
  disjoint F k
  disjoint F l
  disjoint F y
  disjoint I j
  disjoint I k
  disjoint I l
  disjoint I y
  disjoint I z
  disjoint L j
  disjoint j x
  disjoint R k
  disjoint R l
  disjoint R y
  disjoint R z
  disjoint .x. j
  disjoint .x. k
  disjoint .x. l
  disjoint .x. y
  disjoint W j
  disjoint W k
  disjoint W l
  disjoint W y
  disjoint X j
  disjoint X k
  disjoint X l
  disjoint X y
  disjoint X z
  disjoint Y j
  disjoint Y k
  disjoint Y l
  disjoint Y y
  disjoint Y z
  disjoint .0. j
  disjoint .0. l
  disjoint .0. y
  disjoint j y
  disjoint l x
  disjoint l y
  disjoint x z
  assert |- ( ( W e. LMod /\ I e. X /\ F : I --> B ) -> ( F LIndF W <-> A. x e. L ( ( W gsum ( x oF .x. F ) ) = .0. -> x = ( I X. { Y } ) ) ) )

  proof
    cW
    clmod
    wcel
    #
    cI
    cX
    wcel
    #
    cI
    cB
    cF
    wf
    #
    w3a
    #
    vk
    cv
    #
    vj
    cv
    #
    cF
    cfv
    #
    c.x
    co
    #
    cF
    cI
    @5
    csn
    #
    cdif
    #
    cima
    #
    cW
    clspn
    cfv
    #
    cfv
    #
    wcel
    #
    wn
    #
    vk
    cR
    cbs
    cfv
    #
    cY
    csn
    #
    cdif
    #
    wral
    #
    vj
    cI
    wral
    cW
    vx
    cv
    #
    cF
    c.x
    cof
    #
    co
    #
    cgsu
    co
    #
    c.0
    wceq
    #
    @5
    @19
    cfv
    #
    @5
    cI
    @16
    cxp
    #
    cfv
    #
    wceq
    #
    wi
    #
    vx
    cL
    wral
    #
    vj
    cI
    wral
    #
    cF
    cW
    clindf
    wbr
    @23
    @19
    @25
    wceq
    #
    wi
    #
    vx
    cL
    wral
    #
    @3
    @18
    @29
    vj
    cI
    @3
    @5
    cI
    wcel
    #
    wa
    #
    vl
    cv
    #
    cR
    cminusg
    cfv
    #
    cfv
    #
    @6
    c.x
    co
    #
    @12
    wcel
    #
    wn
    #
    vl
    @17
    wral
    #
    @23
    @24
    cY
    wceq
    #
    wi
    #
    vx
    cL
    wral
    #
    @18
    @29
    @42
    @40
    @36
    cY
    wceq
    #
    wi
    #
    vl
    @15
    wral
    #
    @35
    @45
    @40
    vl
    @15
    cY
    raldifsni
    @35
    vy
    cv
    #
    cY
    cfsupp
    wbr
    #
    @39
    cW
    @49
    cF
    @9
    cres
    #
    @20
    co
    #
    cgsu
    co
    #
    wceq
    #
    wa
    #
    @46
    wi
    #
    vy
    @15
    @9
    cmap
    co
    #
    wral
    #
    vl
    @15
    wral
    #
    @44
    vx
    vz
    cv
    #
    cY
    cfsupp
    wbr
    #
    vz
    @15
    cI
    cmap
    co
    #
    crab
    #
    wral
    #
    @48
    @45
    @35
    @59
    @19
    cY
    cfsupp
    wbr
    #
    @44
    wi
    #
    vx
    @62
    wral
    #
    @64
    @35
    @59
    @49
    @5
    @36
    cop
    #
    csn
    #
    cun
    #
    cY
    cfsupp
    wbr
    #
    cW
    @70
    cF
    @20
    co
    #
    cgsu
    co
    #
    c.0
    wceq
    #
    @5
    @70
    cfv
    #
    cY
    wceq
    #
    wi
    #
    wi
    #
    vy
    @57
    wral
    vl
    @15
    wral
    #
    @67
    @35
    @56
    @78
    vl
    vy
    @15
    @57
    @35
    @36
    @15
    wcel
    #
    @49
    @57
    wcel
    #
    wa
    #
    wa
    #
    @50
    @54
    @46
    wi
    #
    wi
    #
    @50
    @77
    wi
    @56
    @78
    @83
    @50
    @84
    @77
    @35
    @82
    @50
    @84
    @77
    wb
    @35
    @82
    @50
    wa
    #
    wa
    #
    @54
    @74
    @46
    @76
    @87
    @54
    @36
    @6
    c.x
    co
    #
    cW
    cminusg
    cfv
    #
    cfv
    #
    @53
    wceq
    #
    @53
    @88
    cW
    cplusg
    cfv
    #
    co
    #
    c.0
    wceq
    #
    @74
    @87
    @39
    @90
    @53
    @87
    @0
    @80
    @6
    cB
    wcel
    #
    @39
    @90
    wceq
    @0
    @1
    @2
    @34
    @86
    simpll1
    #
    @35
    @80
    @81
    @50
    simprll
    #
    @35
    @95
    @86
    @2
    @0
    @34
    @95
    @1
    cI
    cB
    @5
    cF
    ffvelrn
    3ad2antl3
    adantr
    #
    cB
    @36
    c.x
    cR
    @15
    @37
    @89
    cW
    @6
    islindf4.b
    islindf4.r
    islindf4.t
    @89
    eqid
    #
    @37
    eqid
    #
    @15
    eqid
    #
    lmodvsinv
    syl3anc
    eqeq1d
    @87
    cW
    cgrp
    wcel
    #
    @88
    cB
    wcel
    #
    @53
    cB
    wcel
    @91
    @94
    wb
    @87
    @0
    @102
    @96
    cW
    lmodgrp
    syl
    @87
    @0
    @80
    @95
    @103
    @96
    @97
    @98
    @36
    c.x
    cR
    @15
    cB
    cW
    @6
    islindf4.b
    islindf4.r
    islindf4.t
    @101
    lmodvscl
    syl3anc
    #
    @87
    @9
    cB
    @52
    cW
    cvv
    c.0
    islindf4.b
    islindf4.z
    @87
    @0
    cW
    ccmn
    wcel
    #
    @96
    cW
    lmodcmn
    syl
    #
    @87
    @1
    @9
    cvv
    wcel
    #
    @0
    @1
    @2
    @34
    @86
    simpll2
    #
    cI
    @8
    cX
    difexg
    #
    syl
    #
    @87
    cB
    c.x
    cR
    @49
    @51
    @9
    @15
    cvv
    cW
    islindf4.r
    @101
    islindf4.t
    islindf4.b
    @96
    @87
    @81
    @9
    @15
    @49
    wf
    #
    @35
    @80
    @81
    @50
    simprlr
    @49
    @15
    @9
    elmapi
    #
    syl
    #
    @87
    @2
    @9
    cI
    wss
    #
    @9
    cB
    @51
    wf
    #
    @0
    @1
    @2
    @34
    @86
    simpll3
    #
    cI
    @8
    difss
    #
    cI
    cB
    @9
    cF
    fssres
    #
    sylancl
    #
    @110
    lcomf
    @87
    cB
    c.x
    cR
    @49
    @51
    @9
    @15
    cvv
    cW
    cY
    c.0
    islindf4.r
    @101
    islindf4.t
    islindf4.b
    @96
    @113
    @119
    @110
    islindf4.z
    islindf4.y
    @35
    @82
    @50
    simprr
    lcomfsupp
    gsumcl
    cB
    @92
    cW
    @89
    @88
    @53
    c.0
    islindf4.b
    @92
    eqid
    #
    islindf4.z
    @99
    grpinvid2
    syl3anc
    @87
    @93
    @73
    c.0
    @87
    @73
    cW
    @72
    @9
    cres
    #
    cgsu
    co
    #
    cW
    @72
    @8
    cres
    #
    cgsu
    co
    #
    @92
    co
    @93
    @87
    cI
    cB
    @9
    @8
    @92
    @72
    cW
    cX
    c.0
    islindf4.b
    islindf4.z
    @120
    @106
    @108
    @87
    cB
    c.x
    cR
    @70
    cF
    cI
    @15
    cX
    cW
    islindf4.r
    @101
    islindf4.t
    islindf4.b
    @96
    @87
    @111
    @34
    @80
    cI
    @15
    @70
    wf
    #
    @113
    @3
    @34
    @86
    simplr
    #
    @97
    cI
    @15
    @49
    @5
    @36
    fsnunf2
    syl3anc
    #
    @116
    @108
    lcomf
    #
    @87
    cB
    c.x
    cR
    @70
    cF
    cI
    @15
    cX
    cW
    cY
    c.0
    islindf4.r
    @101
    islindf4.t
    islindf4.b
    @96
    @127
    @116
    @108
    islindf4.z
    islindf4.y
    @35
    @82
    @50
    @71
    @83
    @50
    @71
    @83
    @34
    @80
    wa
    #
    @49
    wfun
    #
    @5
    @49
    cdm
    #
    wnel
    #
    wa
    #
    wa
    #
    @50
    @71
    wb
    @83
    @129
    @133
    @35
    @34
    @82
    @80
    @3
    @34
    simpr
    @80
    @81
    simpl
    anim12i
    @82
    @133
    @35
    @81
    @133
    @80
    @81
    @130
    @132
    @49
    @15
    @9
    elmapfun
    @81
    @111
    @132
    @112
    @111
    @131
    @9
    wceq
    #
    @132
    @9
    @15
    @49
    fdm
    @135
    @132
    @5
    @9
    wcel
    #
    wn
    #
    @135
    @5
    cI
    neldifsnd
    @132
    @5
    @131
    wcel
    #
    wn
    #
    @135
    @137
    @5
    @131
    df-nel
    @135
    @138
    @136
    @131
    @9
    @5
    eleq2
    notbid
    syl5bb
    mpbird
    syl
    syl
    jca
    adantl
    adantl
    jca
    @134
    @71
    @50
    @49
    cI
    @15
    @5
    @36
    cY
    funsnfsupp
    bicomd
    syl
    #
    biimpd
    impr
    lcomfsupp
    @9
    @8
    cin
    #
    c0
    wceq
    @87
    @141
    @8
    @9
    cin
    c0
    @9
    @8
    incom
    @8
    cI
    disjdif
    eqtri
    a1i
    @87
    @34
    cI
    @9
    @8
    cun
    #
    wceq
    @126
    @34
    @142
    cI
    cI
    @5
    difsnid
    eqcomd
    syl
    gsumsplit
    @87
    @122
    @53
    @124
    @88
    @92
    @87
    @121
    @52
    cW
    cgsu
    @87
    @121
    @70
    @9
    cres
    #
    @51
    @20
    co
    #
    @52
    @87
    @70
    cvv
    wcel
    cF
    cvv
    wcel
    #
    @121
    @144
    wceq
    @49
    @69
    vy
    vex
    @68
    snex
    unex
    @35
    @145
    @86
    @35
    @2
    @1
    @145
    @0
    @1
    @2
    @34
    simpl3
    #
    @0
    @1
    @2
    @34
    simpl2
    cI
    cB
    cX
    cF
    fex
    syl2anc
    adantr
    @9
    c.x
    @70
    cF
    cvv
    cvv
    offres
    sylancr
    @87
    @143
    @49
    @51
    @20
    @87
    @49
    @9
    wfn
    #
    @137
    @143
    @49
    wceq
    @87
    @111
    @147
    @113
    @9
    @15
    @49
    ffn
    syl
    #
    @5
    cI
    neldifsn
    #
    @9
    @49
    @5
    @36
    fsnunres
    sylancl
    oveq1d
    eqtrd
    oveq2d
    @87
    @124
    cW
    vx
    @8
    @88
    cmpt
    #
    cgsu
    co
    #
    @88
    @87
    @123
    @150
    cW
    cgsu
    @87
    @123
    @5
    @5
    @72
    cfv
    #
    cop
    #
    csn
    #
    @5
    @88
    cop
    #
    csn
    #
    @150
    @87
    @72
    cI
    wfn
    #
    @34
    @123
    @154
    wceq
    @87
    cI
    cB
    @72
    wf
    @157
    @128
    cI
    cB
    @72
    ffn
    syl
    @126
    cI
    @5
    @72
    fnressn
    syl2anc
    @87
    @153
    @155
    @87
    @152
    @88
    @5
    @87
    @152
    @75
    @6
    c.x
    co
    #
    @88
    @87
    @70
    cI
    wfn
    #
    cF
    cI
    wfn
    #
    @1
    @34
    @152
    @158
    wceq
    @87
    @125
    @159
    @127
    cI
    @15
    @70
    ffn
    syl
    @87
    @2
    @160
    @116
    cI
    cB
    cF
    ffn
    syl
    @108
    @126
    cI
    c.x
    @70
    cF
    cX
    @5
    fnfvof
    syl22anc
    @87
    @75
    @36
    @6
    c.x
    @87
    @147
    @139
    @75
    @36
    wceq
    #
    @148
    @147
    @138
    @136
    @149
    @147
    @131
    @9
    @5
    @9
    @49
    fndm
    eleq2d
    mtbiri
    @5
    cvv
    wcel
    #
    @36
    cvv
    wcel
    @139
    @161
    vj
    vex
    #
    vl
    vex
    @49
    cvv
    cvv
    @5
    @36
    fsnunfv
    mp3an12
    3syl
    #
    oveq1d
    eqtrd
    opeq2d
    sneqd
    @156
    @150
    wceq
    #
    @87
    @162
    @88
    cvv
    wcel
    @165
    @163
    @36
    @6
    c.x
    ovex
    vx
    @5
    @88
    cvv
    cvv
    fmptsn
    mp2an
    a1i
    3eqtrd
    oveq2d
    @87
    cW
    cmnd
    wcel
    #
    @162
    @103
    @151
    @88
    wceq
    @87
    @105
    @166
    @106
    cW
    cmnmnd
    syl
    @162
    @87
    @163
    a1i
    @104
    @88
    cB
    @88
    vx
    cW
    @5
    cvv
    islindf4.b
    @19
    @5
    wceq
    @88
    eqidd
    gsumsn
    syl3anc
    eqtrd
    oveq12d
    eqtr2d
    eqeq1d
    3bitrd
    @87
    @36
    @75
    cY
    @87
    @75
    @36
    @164
    eqcomd
    eqeq1d
    imbi12d
    anassrs
    pm5.74da
    @56
    @85
    wb
    @83
    @50
    @54
    @46
    impexp
    a1i
    @83
    @71
    @50
    @77
    @83
    @50
    @71
    @140
    bicomd
    imbi1d
    3bitr4d
    2ralbidva
    @34
    @67
    @79
    wb
    @3
    @66
    @78
    vl
    @15
    cI
    vx
    vy
    @5
    @19
    @70
    wceq
    #
    @65
    @71
    @44
    @77
    @19
    @70
    cY
    cfsupp
    breq1
    @167
    @23
    @74
    @43
    @76
    @167
    @22
    @73
    c.0
    @167
    @21
    @72
    cW
    cgsu
    @19
    @70
    cF
    @20
    oveq1
    oveq2d
    eqeq1d
    @167
    @24
    @75
    cY
    @5
    @19
    @70
    fveq1
    eqeq1d
    imbi12d
    imbi12d
    ralxpmap
    adantl
    bitr4d
    @61
    @65
    @44
    vx
    vz
    @62
    @60
    @19
    cY
    cfsupp
    breq1
    ralrab
    syl6bbr
    @35
    @47
    @58
    vl
    @15
    @35
    @47
    @55
    vy
    @57
    wrex
    #
    @46
    wi
    @58
    @35
    @40
    @168
    @46
    @40
    @39
    @51
    @9
    cima
    #
    @11
    cfv
    #
    wcel
    @35
    @168
    @12
    @170
    @39
    @10
    @169
    @11
    @169
    @10
    cF
    @9
    resima
    eqcomi
    fveq2i
    eleq2i
    @35
    cB
    cR
    c.x
    vy
    @51
    @9
    @15
    cW
    @11
    @39
    cY
    @11
    eqid
    #
    islindf4.b
    @101
    islindf4.r
    islindf4.y
    islindf4.t
    @35
    @2
    @114
    @115
    @146
    @117
    @118
    sylancl
    @0
    @1
    @2
    @34
    simpl1
    @3
    @107
    @34
    @1
    @0
    @107
    @2
    @109
    3ad2ant2
    adantr
    ellspd
    syl5bb
    imbi1d
    @55
    @46
    vy
    @57
    r19.23v
    syl6bbr
    ralbidv
    @35
    @44
    vx
    cL
    @63
    @35
    @63
    cR
    cI
    cfrlm
    co
    #
    cbs
    cfv
    #
    cL
    @3
    @63
    @173
    wceq
    #
    @34
    @1
    @0
    @174
    @2
    cR
    cvv
    wcel
    @1
    @174
    cR
    cW
    csca
    cfv
    cvv
    islindf4.r
    cW
    csca
    fvex
    eqeltri
    @63
    cR
    vz
    @172
    cI
    @15
    cvv
    cX
    cY
    @172
    eqid
    #
    @101
    islindf4.y
    @63
    eqid
    frlmbas
    mpan
    3ad2ant2
    adantr
    islindf4.l
    syl6reqr
    raleqdv
    3bitr4d
    syl5bb
    @3
    @18
    @42
    wb
    #
    @34
    @0
    @1
    @176
    @2
    @0
    @14
    @41
    vk
    vl
    @38
    @17
    @17
    @0
    cR
    cgrp
    wcel
    #
    @36
    @17
    wcel
    @38
    @17
    wcel
    cR
    cW
    islindf4.r
    lmodfgrp
    #
    @15
    cR
    @37
    @36
    cY
    @101
    islindf4.y
    @100
    grpinvnzcl
    sylan
    @0
    @4
    @17
    wcel
    #
    wa
    #
    @4
    @37
    cfv
    #
    @17
    wcel
    #
    @4
    @181
    @37
    cfv
    #
    wceq
    #
    @4
    @38
    wceq
    #
    vl
    @17
    wrex
    @0
    @177
    @179
    @182
    @178
    @15
    cR
    @37
    @4
    cY
    @101
    islindf4.y
    @100
    grpinvnzcl
    sylan
    @180
    @183
    @4
    @0
    @177
    @4
    @15
    wcel
    @183
    @4
    wceq
    @179
    @178
    @4
    @15
    @16
    eldifi
    @15
    cR
    @37
    @4
    @101
    @100
    grpinvinv
    syl2an
    eqcomd
    @185
    @184
    vl
    @181
    @17
    @36
    @181
    wceq
    @38
    @183
    @4
    @36
    @181
    @37
    fveq2
    eqeq2d
    rspcev
    syl2anc
    @185
    @14
    @41
    wb
    @0
    @185
    @13
    @40
    @185
    @7
    @39
    @12
    @4
    @38
    @6
    c.x
    oveq1
    eleq1d
    notbid
    adantl
    ralxfrd
    3ad2ant1
    adantr
    @35
    @28
    @44
    vx
    cL
    @35
    @19
    cL
    wcel
    #
    wa
    #
    @27
    @43
    @23
    @187
    @26
    cY
    @24
    @187
    @34
    @26
    cY
    wceq
    @3
    @34
    @186
    simplr
    cI
    cY
    @5
    cY
    cR
    c0g
    cfv
    cvv
    islindf4.y
    cR
    c0g
    fvex
    eqeltri
    #
    fvconst2
    syl
    eqeq2d
    imbi2d
    ralbidva
    3bitr4d
    ralbidva
    vj
    cB
    cR
    c.x
    vk
    cF
    cI
    @11
    @15
    cW
    cX
    clmod
    cY
    islindf4.b
    islindf4.t
    @171
    islindf4.r
    @101
    islindf4.y
    islindf2
    @3
    @33
    @23
    @27
    vj
    cI
    wral
    #
    wi
    #
    vx
    cL
    wral
    #
    @30
    @3
    @32
    @190
    vx
    cL
    @3
    @186
    wa
    #
    @31
    @189
    @23
    @192
    @19
    cI
    wfn
    #
    @25
    cI
    wfn
    #
    @31
    @189
    wb
    @192
    cI
    @15
    @19
    wf
    #
    @193
    @1
    @0
    @186
    @195
    @2
    cL
    cR
    @172
    cI
    @15
    cX
    @19
    @175
    @101
    islindf4.l
    frlmbasf
    3ad2antl2
    cI
    @15
    @19
    ffn
    syl
    cY
    cvv
    wcel
    @194
    @188
    cI
    cY
    cvv
    fnconstg
    ax-mp
    vj
    cI
    @19
    @25
    eqfnfv
    sylancl
    imbi2d
    ralbidva
    @191
    @28
    vj
    cI
    wral
    #
    vx
    cL
    wral
    @30
    @196
    @190
    vx
    cL
    @23
    @27
    vj
    cI
    r19.21v
    ralbii
    @28
    vx
    vj
    cL
    cI
    ralcom
    bitr3i
    syl6bb
    3bitr4d
end
