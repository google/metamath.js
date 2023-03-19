include "cfv.mm"
include "csymg.mm"
include "cbs.mm"
include "cv.mm"
include "czrh.mm"
include "cpsgn.mm"
include "ccom.mm"
include "cmgp.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmulr.mm"
include "cevpm.mm"
include "cres.mm"
include "cdif.mm"
include "cplusg.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "mdetleib.mm"
include "syl.mm"
include "crg.mm"
include "ccmn.mm"
include "ccrg.mm"
include "crngring.mm"
include "ringcmn.mm"
include "cfn.mm"
include "cvv.mm"
include "wa.mm"
include "matrcl.mm"
include "simpld.mm"
include "symgbasfi.mm"
include "adantr.mm"
include "cmhm.mm"
include "wf.mm"
include "zrhpsgnmhm.mm"
include "syl2anc.mm"
include "mgpbas.mm"
include "mhmf.mm"
include "ffvelrnda.mm"
include "crngmgp.mm"
include "cxp.mm"
include "cmap.mm"
include "matbas2i.mm"
include "elmapi.mm"
include "ad2antrr.mm"
include "wf1o.mm"
include "symgbasf1o.mm"
include "adantl.mm"
include "f1of.mm"
include "simpr.mm"
include "fovrnd.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "cin.mm"
include "c0.mm"
include "disjdif.mm"
include "a1i.mm"
include "cun.mm"
include "wss.mm"
include "evpmss.mm"
include "undif.mm"
include "mpbi.mm"
include "eqcomi.mm"
include "gsummptfidmsplitres.mm"
include "cminusg.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "cur.mm"
include "zrhpsgnevpm.mm"
include "oveq1d.mm"
include "sseli.mm"
include "sylan2.mm"
include "ringlidm.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "difss.mm"
include "zrhpsgnodpm.mm"
include "eldifi.mm"
include "ringnegl.mm"
include "eqidd.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grpinvf.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "eqtr4d.mm"
include "cabl.mm"
include "ringabl.mm"
include "difssd.mm"
include "ssfi.mm"
include "gsummptfidminv.mm"
include "cpr.mm"
include "cpmtr.mm"
include "crn.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "prssi.mm"
include "wne.mm"
include "pr2nelem.mm"
include "pmtrrn.mm"
include "pmtrodpm.mm"
include "evpmodpmf1o.mm"
include "gsummptfif1o.mm"
include "wi.mm"
include "weq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "c1.mm"
include "cneg.mm"
include "symggrp.mm"
include "symgtrf.mm"
include "sseldi.mm"
include "grpcl.mm"
include "cmul.mm"
include "ccnfld.mm"
include "cress.mm"
include "cghm.mm"
include "psgnghm2.mm"
include "prex.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "ghmlin.mm"
include "psgnpmtr.mm"
include "psgnevpm.mm"
include "sylan.mm"
include "oveq12d.mm"
include "neg1cn.mm"
include "mulid1i.mm"
include "syl6eq.mm"
include "psgnodpmr.mm"
include "chvarv.mm"
include "fveq1.mm"
include "mpteq2dv.mm"
include "fveq1d.mm"
include "cbvmptv.mm"
include "symgov.mm"
include "fvco3.mm"
include "pmtrprfv.mm"
include "syl13anc.mm"
include "wral.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "oveq1.mm"
include "syl5ibrcom.mm"
include "prcom.mm"
include "fveq2i.mm"
include "fveq1i.mm"
include "necomd.mm"
include "a1dd.mm"
include "w3a.mm"
include "cid.mm"
include "cdm.mm"
include "wn.mm"
include "wo.mm"
include "neanior.mm"
include "elpri.mm"
include "orcomd.mm"
include "con3i.mm"
include "sylbi.mm"
include "3adant1.mm"
include "pmtrmvd.mm"
include "3ad2ant1.mm"
include "neleqtrrd.mm"
include "wb.mm"
include "wfn.mm"
include "pmtrf.mm"
include "ffn.mm"
include "fnelnfp.mm"
include "necon2bbid.mm"
include "mpbird.mm"
include "3exp.mm"
include "pm2.61dne.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "grprinv.mm"

theorem mdetralt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cI: class I
  let cJ: class J
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  let vc: setvar c
  let vp: setvar p
  let vq: setvar q
  assume mdetralt.d: |- D = ( N maDet R )
  assume mdetralt.a: |- A = ( N Mat R )
  assume mdetralt.b: |- B = ( Base ` A )
  assume mdetralt.z: |- .0. = ( 0g ` R )
  assume mdetralt.r: |- ( ph -> R e. CRing )
  assume mdetralt.x: |- ( ph -> X e. B )
  assume mdetralt.i: |- ( ph -> I e. N )
  assume mdetralt.j: |- ( ph -> J e. N )
  assume mdetralt.ij: |- ( ph -> I =/= J )
  assume mdetralt.eq: |- ( ph -> A. a e. N ( I X a ) = ( J X a ) )

  disjoint I a
  disjoint J a
  disjoint N a
  disjoint X a
  disjoint c ph
  disjoint p ph
  disjoint ph q
  disjoint c p
  disjoint c q
  disjoint p q
  disjoint I c
  disjoint I p
  disjoint I q
  disjoint a c
  disjoint a p
  disjoint a q
  disjoint J c
  disjoint J p
  disjoint J q
  disjoint N c
  disjoint N p
  disjoint N q
  disjoint R c
  disjoint R p
  disjoint R q
  disjoint X c
  disjoint X p
  disjoint X q
  assert |- ( ph -> ( D ` X ) = .0. )

  proof
    wph
    cX
    cD
    cfv
    #
    cR
    vp
    cN
    csymg
    cfv
    #
    cbs
    cfv
    #
    vp
    cv
    #
    cR
    czrh
    cfv
    #
    cN
    cpsgn
    cfv
    #
    ccom
    #
    cfv
    #
    cR
    cmgp
    cfv
    #
    vc
    cN
    vc
    cv
    #
    @3
    cfv
    #
    @9
    cX
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    @16
    cN
    cevpm
    cfv
    #
    cres
    #
    cgsu
    co
    #
    cR
    @16
    @2
    @18
    cdif
    #
    cres
    #
    cgsu
    co
    #
    cR
    cplusg
    cfv
    #
    co
    #
    c.0
    wph
    cX
    cB
    wcel
    #
    @0
    @17
    wceq
    mdetralt.x
    vc
    cA
    cB
    cD
    @2
    cR
    @5
    @14
    @8
    cX
    cN
    @4
    vp
    mdetralt.d
    mdetralt.a
    mdetralt.b
    @2
    eqid
    #
    @4
    eqid
    #
    @5
    eqid
    #
    @14
    eqid
    #
    @8
    eqid
    #
    mdetleib
    syl
    wph
    @2
    cR
    cbs
    cfv
    #
    @18
    @21
    @24
    vp
    @16
    cR
    @15
    @32
    eqid
    #
    @24
    eqid
    #
    wph
    cR
    crg
    wcel
    #
    cR
    ccmn
    wcel
    wph
    cR
    ccrg
    wcel
    #
    @35
    mdetralt.r
    cR
    crngring
    syl
    #
    cR
    ringcmn
    syl
    #
    wph
    cN
    cfn
    wcel
    #
    @2
    cfn
    wcel
    #
    wph
    @39
    cR
    cvv
    wcel
    #
    wph
    @26
    @39
    @41
    wa
    mdetralt.x
    cA
    cB
    cR
    cN
    cX
    mdetralt.a
    mdetralt.b
    matrcl
    syl
    simpld
    #
    cN
    @2
    @1
    @1
    eqid
    #
    @27
    symgbasfi
    syl
    #
    wph
    @3
    @2
    wcel
    #
    wa
    #
    @35
    @7
    @32
    wcel
    @13
    @32
    wcel
    #
    @15
    @32
    wcel
    wph
    @35
    @45
    @37
    adantr
    wph
    @2
    @32
    @3
    @6
    wph
    @6
    @1
    @8
    cmhm
    co
    wcel
    #
    @2
    @32
    @6
    wf
    wph
    @35
    @39
    @48
    @37
    @42
    cN
    cR
    zrhpsgnmhm
    syl2anc
    @2
    @32
    @1
    @8
    @6
    @27
    @32
    cR
    @8
    @31
    @33
    mgpbas
    #
    mhmf
    syl
    ffvelrnda
    @46
    @32
    vc
    @8
    cN
    @11
    @49
    wph
    @8
    ccmn
    wcel
    #
    @45
    wph
    @36
    @50
    mdetralt.r
    cR
    @8
    @31
    crngmgp
    syl
    adantr
    wph
    @39
    @45
    @42
    adantr
    @46
    @11
    @32
    wcel
    vc
    cN
    @46
    @9
    cN
    wcel
    #
    wa
    @10
    @9
    @32
    cN
    cN
    cX
    wph
    cN
    cN
    cxp
    #
    @32
    cX
    wf
    #
    @45
    @51
    wph
    cX
    @32
    @52
    cmap
    co
    wcel
    #
    @53
    wph
    @26
    @54
    mdetralt.x
    cA
    cB
    cR
    @32
    cX
    cN
    mdetralt.a
    @33
    mdetralt.b
    matbas2i
    syl
    cX
    @32
    @52
    elmapi
    syl
    ad2antrr
    @46
    cN
    cN
    @9
    @3
    @46
    cN
    cN
    @3
    wf1o
    #
    cN
    cN
    @3
    wf
    #
    @45
    @55
    wph
    cN
    @2
    @3
    @1
    @43
    @27
    symgbasf1o
    adantl
    cN
    cN
    @3
    f1of
    syl
    #
    ffvelrnda
    @46
    @51
    simpr
    fovrnd
    ralrimiva
    gsummptcl
    #
    @32
    cR
    @14
    @7
    @13
    @33
    @30
    ringcl
    syl3anc
    @18
    @21
    cin
    c0
    wceq
    wph
    @18
    @2
    disjdif
    a1i
    @2
    @18
    @21
    cun
    #
    wceq
    wph
    @59
    @2
    @18
    @2
    wss
    #
    @59
    @2
    wceq
    cN
    @2
    @1
    @43
    @27
    evpmss
    #
    @18
    @2
    undif
    mpbi
    eqcomi
    a1i
    @16
    eqid
    gsummptfidmsplitres
    wph
    @25
    cR
    vp
    @18
    @13
    cmpt
    #
    cgsu
    co
    #
    @63
    cR
    cminusg
    cfv
    #
    cfv
    #
    @24
    co
    #
    c.0
    wph
    @20
    @63
    @23
    @65
    @24
    wph
    @19
    @62
    cR
    cgsu
    wph
    @19
    vp
    @18
    @15
    cmpt
    #
    @62
    @60
    @19
    @67
    wceq
    @61
    vp
    @2
    @18
    @15
    resmpt
    ax-mp
    wph
    vp
    @18
    @15
    @13
    wph
    @3
    @18
    wcel
    #
    wa
    #
    @15
    cR
    cur
    cfv
    #
    @13
    @14
    co
    #
    @13
    @69
    @7
    @70
    @13
    @14
    @69
    @35
    @39
    @68
    @7
    @70
    wceq
    wph
    @35
    @68
    @37
    adantr
    #
    wph
    @39
    @68
    @42
    adantr
    #
    wph
    @68
    simpr
    cR
    @5
    @70
    @3
    cN
    @4
    @28
    @29
    @70
    eqid
    #
    zrhpsgnevpm
    syl3anc
    oveq1d
    @69
    @35
    @47
    @71
    @13
    wceq
    @72
    @68
    wph
    @45
    @47
    @18
    @2
    @3
    @61
    sseli
    #
    @58
    sylan2
    #
    @32
    cR
    @14
    @70
    @13
    @33
    @30
    @74
    ringlidm
    syl2anc
    eqtrd
    mpteq2dva
    syl5eq
    oveq2d
    wph
    @23
    cR
    @64
    vp
    @21
    @13
    cmpt
    #
    ccom
    #
    cgsu
    co
    cR
    @77
    cgsu
    co
    #
    @64
    cfv
    @65
    wph
    @22
    @78
    cR
    cgsu
    wph
    @22
    vp
    @21
    @15
    cmpt
    #
    @78
    @21
    @2
    wss
    #
    @22
    @80
    wceq
    @2
    @18
    difss
    vp
    @2
    @21
    @15
    resmpt
    ax-mp
    wph
    @80
    vp
    @21
    @13
    @64
    cfv
    #
    cmpt
    @78
    wph
    vp
    @21
    @15
    @82
    wph
    @3
    @21
    wcel
    #
    wa
    #
    @15
    @70
    @64
    cfv
    #
    @13
    @14
    co
    @82
    @84
    @7
    @85
    @13
    @14
    @84
    @35
    @39
    @83
    @7
    @85
    wceq
    wph
    @35
    @83
    @37
    adantr
    #
    wph
    @39
    @83
    @42
    adantr
    wph
    @83
    simpr
    @2
    cR
    @5
    @70
    @3
    @64
    cN
    @4
    @28
    @29
    @74
    @27
    @64
    eqid
    #
    zrhpsgnodpm
    syl3anc
    oveq1d
    @84
    @32
    cR
    @14
    @70
    @64
    @13
    @33
    @30
    @74
    @87
    @86
    @83
    wph
    @45
    @47
    @3
    @2
    @18
    eldifi
    @58
    sylan2
    #
    ringnegl
    eqtrd
    mpteq2dva
    wph
    vp
    vq
    @21
    @32
    @13
    vq
    cv
    #
    @64
    cfv
    @82
    @77
    @64
    @88
    wph
    @77
    eqidd
    #
    wph
    vq
    @32
    @32
    @64
    wph
    cR
    cgrp
    wcel
    #
    @32
    @32
    @64
    wf
    wph
    @35
    @91
    @37
    cR
    ringgrp
    syl
    #
    @32
    cR
    @64
    @33
    @87
    grpinvf
    syl
    feqmptd
    @89
    @13
    @64
    fveq2
    fmptco
    eqtr4d
    syl5eq
    oveq2d
    wph
    vp
    @21
    @32
    @13
    @77
    cR
    @64
    c.0
    @33
    mdetralt.z
    @87
    wph
    @35
    cR
    cabl
    wcel
    @37
    cR
    ringabl
    syl
    wph
    @40
    @81
    @21
    cfn
    wcel
    @44
    wph
    @2
    @18
    difssd
    @2
    @21
    ssfi
    syl2anc
    #
    @88
    @77
    eqid
    #
    gsummptfidminv
    wph
    @79
    @63
    @64
    wph
    @79
    cR
    @77
    vq
    @18
    cI
    cJ
    cpr
    #
    cN
    cpmtr
    cfv
    #
    cfv
    #
    @89
    @1
    cplusg
    cfv
    #
    co
    #
    cmpt
    #
    ccom
    #
    cgsu
    co
    @63
    wph
    @32
    @18
    vp
    @77
    cR
    @100
    @21
    @13
    @33
    @38
    @93
    wph
    @47
    vp
    @21
    @88
    ralrimiva
    @94
    wph
    @39
    @97
    @21
    wcel
    #
    @18
    @21
    @100
    wf1o
    @42
    wph
    @39
    @97
    @96
    crn
    #
    wcel
    #
    @102
    @42
    wph
    @39
    @95
    cN
    wss
    #
    @95
    c2o
    cen
    wbr
    #
    @104
    @42
    wph
    cI
    cN
    wcel
    #
    cJ
    cN
    wcel
    #
    @105
    mdetralt.i
    mdetralt.j
    cI
    cJ
    cN
    prssi
    syl2anc
    #
    wph
    @107
    @108
    cI
    cJ
    wne
    #
    @106
    mdetralt.i
    mdetralt.j
    mdetralt.ij
    cI
    cJ
    cN
    cN
    pr2nelem
    syl3anc
    #
    cN
    @95
    @103
    @96
    cfn
    @96
    eqid
    #
    @103
    eqid
    #
    pmtrrn
    syl3anc
    #
    cN
    @2
    @1
    @103
    @97
    @43
    @27
    @113
    pmtrodpm
    syl2anc
    cN
    @2
    @1
    vq
    @97
    @43
    @27
    evpmodpmf1o
    syl2anc
    gsummptfif1o
    wph
    @101
    @62
    cR
    cgsu
    wph
    @101
    vq
    @18
    @8
    vc
    cN
    @9
    @99
    cfv
    #
    @9
    cX
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    vp
    @18
    @8
    vc
    cN
    @9
    @97
    @3
    @98
    co
    #
    cfv
    #
    @9
    cX
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    @62
    wph
    vq
    vp
    @18
    @21
    @99
    @13
    @118
    @100
    @77
    @69
    @120
    @21
    wcel
    #
    wi
    wph
    @89
    @18
    wcel
    #
    wa
    #
    @99
    @21
    wcel
    #
    wi
    vp
    vq
    vp
    vq
    weq
    #
    @69
    @128
    @126
    @129
    @130
    @68
    @127
    wph
    @3
    @89
    @18
    eleq1
    anbi2d
    @130
    @120
    @99
    @21
    @3
    @89
    @97
    @98
    oveq2
    eleq1d
    imbi12d
    @69
    @39
    @120
    @2
    wcel
    #
    @120
    @5
    cfv
    #
    c1
    cneg
    #
    wceq
    @126
    @73
    @69
    @1
    cgrp
    wcel
    #
    @97
    @2
    wcel
    #
    @45
    @131
    wph
    @134
    @68
    wph
    @39
    @134
    @42
    cN
    @1
    cfn
    @43
    symggrp
    syl
    adantr
    @69
    @103
    @2
    @97
    @2
    cN
    @103
    @1
    @113
    @43
    @27
    symgtrf
    wph
    @104
    @68
    @114
    adantr
    #
    sseldi
    #
    @68
    @45
    wph
    @75
    adantl
    #
    @2
    @98
    @1
    @97
    @3
    @27
    @98
    eqid
    #
    grpcl
    syl3anc
    @69
    @132
    @97
    @5
    cfv
    #
    @3
    @5
    cfv
    #
    cmul
    co
    #
    @133
    @69
    @5
    @1
    ccnfld
    cmgp
    cfv
    #
    c1
    @133
    cpr
    #
    cress
    co
    #
    cghm
    co
    wcel
    #
    @135
    @45
    @132
    @142
    wceq
    wph
    @146
    @68
    wph
    @39
    @146
    @42
    cN
    @1
    @145
    @5
    @43
    @29
    @145
    eqid
    #
    psgnghm2
    syl
    adantr
    @137
    @138
    @98
    cmul
    @1
    @145
    @97
    @5
    @3
    @2
    @27
    @139
    @144
    cvv
    wcel
    cmul
    @145
    cplusg
    cfv
    wceq
    c1
    @133
    prex
    @144
    cmul
    @143
    @145
    cvv
    @147
    ccnfld
    cmul
    @143
    @143
    eqid
    cnfldmul
    mgpplusg
    ressplusg
    ax-mp
    ghmlin
    syl3anc
    @69
    @142
    @133
    c1
    cmul
    co
    @133
    @69
    @140
    @133
    @141
    c1
    cmul
    @69
    @104
    @140
    @133
    wceq
    @136
    cN
    @97
    @103
    @1
    @5
    @43
    @113
    @29
    psgnpmtr
    syl
    wph
    @39
    @68
    @141
    c1
    wceq
    @42
    cN
    @2
    @1
    @3
    @5
    @43
    @27
    @29
    psgnevpm
    sylan
    oveq12d
    @133
    neg1cn
    mulid1i
    syl6eq
    eqtrd
    cN
    @2
    @1
    @120
    @5
    @43
    @27
    @29
    psgnodpmr
    syl3anc
    chvarv
    wph
    @100
    eqidd
    @90
    @3
    @99
    wceq
    #
    @12
    @117
    @8
    cgsu
    @148
    vc
    cN
    @11
    @116
    @148
    @10
    @115
    @9
    cX
    @9
    @3
    @99
    fveq1
    oveq1d
    mpteq2dv
    oveq2d
    fmptco
    @119
    @125
    wceq
    wph
    vq
    vp
    @18
    @118
    @124
    vq
    vp
    weq
    #
    @117
    @123
    @8
    cgsu
    @149
    vc
    cN
    @116
    @122
    @149
    @115
    @121
    @9
    cX
    @149
    @9
    @99
    @120
    @89
    @3
    @97
    @98
    oveq2
    fveq1d
    oveq1d
    mpteq2dv
    oveq2d
    cbvmptv
    a1i
    wph
    vp
    @18
    @124
    @13
    @69
    @123
    @12
    @8
    cgsu
    @69
    vc
    cN
    @122
    @11
    @69
    @51
    wa
    #
    @122
    @10
    @97
    cfv
    #
    @9
    cX
    co
    #
    @11
    @150
    @121
    @151
    @9
    cX
    @150
    @121
    @9
    @97
    @3
    ccom
    #
    cfv
    #
    @151
    @150
    @9
    @120
    @153
    @150
    @135
    @45
    @120
    @153
    wceq
    @69
    @135
    @51
    @137
    adantr
    @69
    @45
    @51
    @138
    adantr
    cN
    @2
    @98
    @1
    @97
    @3
    @43
    @27
    @139
    symgov
    syl2anc
    fveq1d
    @69
    @56
    @51
    @154
    @151
    wceq
    @68
    wph
    @45
    @56
    @75
    @57
    sylan2
    #
    cN
    cN
    @9
    @97
    @3
    fvco3
    sylan
    eqtrd
    oveq1d
    @150
    @152
    @11
    wceq
    #
    @10
    cI
    @150
    @156
    @10
    cI
    wceq
    #
    cI
    @97
    cfv
    #
    @9
    cX
    co
    #
    cI
    @9
    cX
    co
    #
    wceq
    @150
    @159
    cJ
    @9
    cX
    co
    #
    @160
    @150
    @158
    cJ
    @9
    cX
    wph
    @158
    cJ
    wceq
    #
    @68
    @51
    wph
    @39
    @107
    @108
    @110
    @162
    @42
    mdetralt.i
    mdetralt.j
    mdetralt.ij
    cN
    @96
    cfn
    cI
    cJ
    @112
    pmtrprfv
    syl13anc
    ad2antrr
    oveq1d
    @150
    @51
    cI
    va
    cv
    #
    cX
    co
    #
    cJ
    @163
    cX
    co
    #
    wceq
    #
    va
    cN
    wral
    #
    @160
    @161
    wceq
    #
    @69
    @51
    simpr
    wph
    @167
    @68
    @51
    mdetralt.eq
    ad2antrr
    @166
    @168
    va
    @9
    cN
    va
    vc
    weq
    @164
    @160
    @165
    @161
    @163
    @9
    cI
    cX
    oveq2
    @163
    @9
    cJ
    cX
    oveq2
    eqeq12d
    rspcv
    sylc
    #
    eqtr4d
    @157
    @152
    @159
    @11
    @160
    @157
    @151
    @158
    @9
    cX
    @10
    cI
    @97
    fveq2
    oveq1d
    @10
    cI
    @9
    cX
    oveq1
    eqeq12d
    syl5ibrcom
    @150
    @10
    cI
    wne
    #
    @156
    wi
    @10
    cJ
    @150
    @10
    cJ
    wceq
    #
    @156
    @170
    @150
    @156
    @171
    cJ
    @97
    cfv
    #
    @9
    cX
    co
    #
    @161
    wceq
    @150
    @173
    @160
    @161
    wph
    @173
    @160
    wceq
    @68
    @51
    wph
    @172
    cI
    @9
    cX
    wph
    @172
    cJ
    cJ
    cI
    cpr
    #
    @96
    cfv
    #
    cfv
    #
    cI
    cJ
    @97
    @175
    @95
    @174
    @96
    cI
    cJ
    prcom
    fveq2i
    fveq1i
    wph
    @39
    @108
    @107
    cJ
    cI
    wne
    @176
    cI
    wceq
    @42
    mdetralt.j
    mdetralt.i
    wph
    cI
    cJ
    mdetralt.ij
    necomd
    cN
    @96
    cfn
    cJ
    cI
    @112
    pmtrprfv
    syl13anc
    syl5eq
    oveq1d
    ad2antrr
    @169
    eqtrd
    @171
    @152
    @173
    @11
    @161
    @171
    @151
    @172
    @9
    cX
    @10
    cJ
    @97
    fveq2
    oveq1d
    @10
    cJ
    @9
    cX
    oveq1
    eqeq12d
    syl5ibrcom
    a1dd
    @150
    @10
    cJ
    wne
    #
    @170
    @156
    @150
    @177
    @170
    w3a
    #
    @151
    @10
    @9
    cX
    @178
    @151
    @10
    wceq
    @10
    @97
    cid
    cdif
    cdm
    #
    wcel
    #
    wn
    @178
    @179
    @95
    @10
    @177
    @170
    @10
    @95
    wcel
    #
    wn
    #
    @150
    @177
    @170
    wa
    @171
    @157
    wo
    #
    wn
    @182
    @10
    cJ
    @10
    cI
    neanior
    @181
    @183
    @181
    @157
    @171
    @10
    cI
    cJ
    elpri
    orcomd
    con3i
    sylbi
    3adant1
    @150
    @177
    @179
    @95
    wceq
    #
    @170
    wph
    @184
    @68
    @51
    wph
    @39
    @105
    @106
    @184
    @42
    @109
    @111
    cN
    @95
    @96
    cfn
    @112
    pmtrmvd
    syl3anc
    ad2antrr
    3ad2ant1
    neleqtrrd
    @178
    @180
    @151
    @10
    @150
    @177
    @180
    @151
    @10
    wne
    wb
    #
    @170
    @150
    @97
    cN
    wfn
    #
    @10
    cN
    wcel
    @185
    wph
    @186
    @68
    @51
    wph
    cN
    cN
    @97
    wf
    #
    @186
    wph
    @39
    @105
    @106
    @187
    @42
    @109
    @111
    cN
    @95
    @96
    cfn
    @112
    pmtrf
    syl3anc
    cN
    cN
    @97
    ffn
    syl
    ad2antrr
    @69
    cN
    cN
    @9
    @3
    @155
    ffvelrnda
    cN
    @97
    @10
    fnelnfp
    syl2anc
    3ad2ant1
    necon2bbid
    mpbird
    oveq1d
    3exp
    pm2.61dne
    pm2.61dne
    eqtrd
    mpteq2dva
    oveq2d
    mpteq2dva
    3eqtrd
    oveq2d
    eqtrd
    fveq2d
    3eqtrd
    oveq12d
    wph
    @91
    @63
    @32
    wcel
    @66
    c.0
    wceq
    @92
    wph
    @32
    vp
    cR
    @18
    @13
    @33
    @38
    wph
    @40
    @60
    @18
    cfn
    wcel
    @44
    @60
    wph
    @61
    a1i
    @2
    @18
    ssfi
    syl2anc
    wph
    @47
    vp
    @18
    @76
    ralrimiva
    gsummptcl
    @32
    @24
    cR
    @64
    @63
    c.0
    @33
    @34
    mdetralt.z
    @87
    grprinv
    syl2anc
    eqtrd
    3eqtrd
end
