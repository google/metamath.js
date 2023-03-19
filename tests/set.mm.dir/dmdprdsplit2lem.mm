include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cfv.mm"
include "wss.mm"
include "wi.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cuni.mm"
include "cin.mm"
include "wo.mm"
include "cun.mm"
include "wceq.mm"
include "adantr.mm"
include "eleq2d.mm"
include "elun.mm"
include "syl6bb.mm"
include "cres.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "ad2antrr.mm"
include "csubg.mm"
include "wf.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "fssresd.mm"
include "fdm.mm"
include "syl.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "dprdcntz.mm"
include "fvres.mm"
include "ad2antlr.mm"
include "ad2antrl.mm"
include "fveq2d.mm"
include "3sstr3d.mm"
include "exp32.mm"
include "co.mm"
include "dprdub.mm"
include "eqsstr3d.mm"
include "cbs.mm"
include "eqid.mm"
include "dprdssv.mm"
include "ssun2.mm"
include "cntz2ss.mm"
include "sylancr.mm"
include "sstrd.mm"
include "jaod.mm"
include "sylbid.mm"
include "clsm.mm"
include "cmre.mm"
include "cgrp.mm"
include "cacs.mm"
include "dprdgrp.mm"
include "subgacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "difundir.mm"
include "difeq1d.mm"
include "c0.mm"
include "simpr.mm"
include "snssd.mm"
include "sslin.mm"
include "incom.mm"
include "syl5eqr.mm"
include "sseq0.mm"
include "syl2anc.mm"
include "disj3.mm"
include "sylib.mm"
include "uneq2d.mm"
include "3eqtr4a.mm"
include "imaeq2d.mm"
include "imaundi.mm"
include "syl6eq.mm"
include "unieqd.mm"
include "uniun.mm"
include "difss.mm"
include "imass2.mm"
include "uniss.mm"
include "mp2b.mm"
include "cpw.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "mresspw.mm"
include "syl5ss.mm"
include "sspwuni.mm"
include "mrcssidd.mm"
include "dprdspan.mm"
include "df-ima.mm"
include "unieqi.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "sseqtr4d.mm"
include "unss12.mm"
include "mrccl.mm"
include "dprdsubg.mm"
include "lsmunss.mm"
include "eqsstrd.mm"
include "a1i.mm"
include "mrcssd.mm"
include "lsmsubg.mm"
include "syl3anc.mm"
include "mrcsscl.mm"
include "sselda.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "adantl.mm"
include "wb.mm"
include "lsmlub.mm"
include "mpbi2and.mm"
include "ssrin.mm"
include "sseqtrd.mm"
include "lsmub1.mm"
include "subg0cl.mm"
include "sseldd.mm"
include "elind.mm"
include "eqssd.mm"
include "resima2.mm"
include "mp1i.mm"
include "ineq12d.mm"
include "dprddisj.mm"
include "eqtr3d.mm"
include "cv.mm"
include "ciun.mm"
include "wfun.mm"
include "ffun.mm"
include "funiunfv.mm"
include "wral.mm"
include "eldifi.mm"
include "eldifsni.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "subgss.mm"
include "cntzsubg.mm"
include "cntzrecd.mm"
include "lsmdisj3.mm"
include "jca.mm"

theorem dmdprdsplit2lem
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cG: class G
  let cI: class I
  let cK: class K
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let c.po: class .(+)
  let vx: setvar x
  let vy: setvar y
  assume dprdsplit.2: |- ( ph -> S : I --> ( SubGrp ` G ) )
  assume dprdsplit.i: |- ( ph -> ( C i^i D ) = (/) )
  assume dprdsplit.u: |- ( ph -> I = ( C u. D ) )
  assume dmdprdsplit.z: |- Z = ( Cntz ` G )
  assume dmdprdsplit.0: |- .0. = ( 0g ` G )
  assume dmdprdsplit2.1: |- ( ph -> G dom DProd ( S |` C ) )
  assume dmdprdsplit2.2: |- ( ph -> G dom DProd ( S |` D ) )
  assume dmdprdsplit2.3: |- ( ph -> ( G DProd ( S |` C ) ) C_ ( Z ` ( G DProd ( S |` D ) ) ) )
  assume dmdprdsplit2.4: |- ( ph -> ( ( G DProd ( S |` C ) ) i^i ( G DProd ( S |` D ) ) ) = { .0. } )
  assume dmdprdsplit2lem.k: |- K = ( mrCls ` ( SubGrp ` G ) )


  assert |- ( ( ph /\ X e. C ) -> ( ( Y e. I -> ( X =/= Y -> ( S ` X ) C_ ( Z ` ( S ` Y ) ) ) ) /\ ( ( S ` X ) i^i ( K ` U. ( S " ( I \ { X } ) ) ) ) C_ { .0. } ) )

  proof
    wph
    cX
    cC
    wcel
    #
    wa
    #
    cY
    cI
    wcel
    #
    cX
    cY
    wne
    #
    cX
    cS
    cfv
    #
    cY
    cS
    cfv
    #
    cZ
    cfv
    #
    wss
    #
    wi
    #
    wi
    @4
    cS
    cI
    cX
    csn
    #
    cdif
    #
    cima
    #
    cuni
    #
    cK
    cfv
    #
    cin
    #
    c.0
    csn
    #
    wss
    @1
    @2
    cY
    cC
    wcel
    #
    cY
    cD
    wcel
    #
    wo
    #
    @8
    @1
    @2
    cY
    cC
    cD
    cun
    #
    wcel
    @18
    @1
    cI
    @19
    cY
    wph
    cI
    @19
    wceq
    @0
    dprdsplit.u
    adantr
    #
    eleq2d
    cY
    cC
    cD
    elun
    syl6bb
    @1
    @16
    @8
    @17
    @1
    @16
    @3
    @7
    @1
    @16
    @3
    wa
    #
    wa
    #
    cX
    cS
    cC
    cres
    #
    cfv
    #
    cY
    @23
    cfv
    #
    cZ
    cfv
    @4
    @6
    @22
    @23
    cG
    cC
    cX
    cY
    cZ
    wph
    cG
    @23
    cdprd
    cdm
    #
    wbr
    #
    @0
    @21
    dmdprdsplit2.1
    ad2antrr
    wph
    @23
    cdm
    cC
    wceq
    #
    @0
    @21
    wph
    cC
    cG
    csubg
    cfv
    #
    @23
    wf
    @28
    wph
    cI
    @29
    cC
    cS
    dprdsplit.2
    wph
    @19
    cC
    cI
    cC
    cD
    ssun1
    dprdsplit.u
    syl5sseqr
    #
    fssresd
    cC
    @29
    @23
    fdm
    syl
    #
    ad2antrr
    wph
    @0
    @21
    simplr
    @1
    @16
    @3
    simprl
    @1
    @16
    @3
    simprr
    dmdprdsplit.z
    dprdcntz
    @0
    @24
    @4
    wceq
    #
    wph
    @21
    cX
    cC
    cS
    fvres
    #
    ad2antlr
    @22
    @25
    @5
    cZ
    @16
    @25
    @5
    wceq
    @1
    @3
    cY
    cC
    cS
    fvres
    ad2antrl
    fveq2d
    3sstr3d
    exp32
    @1
    @17
    @3
    @7
    @1
    @17
    @3
    wa
    #
    wa
    #
    @4
    cG
    @23
    cdprd
    co
    #
    @6
    @35
    @4
    @24
    @36
    @0
    @32
    wph
    @34
    @33
    ad2antlr
    @35
    @23
    cG
    cC
    cX
    wph
    @27
    @0
    @34
    dmdprdsplit2.1
    ad2antrr
    wph
    @28
    @0
    @34
    @31
    ad2antrr
    wph
    @0
    @34
    simplr
    dprdub
    eqsstr3d
    @35
    @36
    cG
    cS
    cD
    cres
    #
    cdprd
    co
    #
    cZ
    cfv
    #
    @6
    wph
    @36
    @39
    wss
    #
    @0
    @34
    dmdprdsplit2.3
    ad2antrr
    @35
    @38
    cG
    cbs
    cfv
    #
    wss
    @5
    @38
    wss
    @39
    @6
    wss
    @41
    @37
    cG
    @41
    eqid
    #
    dprdssv
    @35
    @5
    cY
    @37
    cfv
    #
    @38
    @17
    @43
    @5
    wceq
    @1
    @3
    cY
    cD
    cS
    fvres
    ad2antrl
    @35
    @37
    cG
    cD
    cY
    wph
    cG
    @37
    @26
    wbr
    #
    @0
    @34
    dmdprdsplit2.2
    ad2antrr
    wph
    @37
    cdm
    cD
    wceq
    #
    @0
    @34
    wph
    cD
    @29
    @37
    wf
    @45
    wph
    cI
    @29
    cD
    cS
    dprdsplit.2
    wph
    @19
    cD
    cI
    cD
    cC
    ssun2
    dprdsplit.u
    syl5sseqr
    fssresd
    cD
    @29
    @37
    fdm
    syl
    ad2antrr
    @1
    @17
    @3
    simprl
    dprdub
    eqsstr3d
    @41
    @38
    @5
    cG
    cZ
    @42
    dmdprdsplit.z
    cntz2ss
    sylancr
    sstrd
    sstrd
    exp32
    jaod
    sylbid
    @1
    @14
    @4
    cS
    cC
    @9
    cdif
    #
    cima
    #
    cuni
    #
    cK
    cfv
    #
    @38
    cG
    clsm
    cfv
    #
    co
    #
    cin
    #
    @15
    @1
    @13
    @51
    wss
    #
    @14
    @52
    wss
    @1
    @29
    @41
    cmre
    cfv
    wcel
    #
    @12
    @51
    wss
    @51
    @29
    wcel
    #
    @53
    @1
    cG
    cgrp
    wcel
    #
    @29
    @41
    cacs
    cfv
    wcel
    @54
    wph
    @56
    @0
    wph
    @27
    @56
    dmdprdsplit2.1
    @23
    cG
    dprdgrp
    syl
    adantr
    #
    @41
    cG
    @42
    subgacs
    @29
    @41
    acsmre
    3syl
    #
    @1
    @12
    @48
    cS
    cD
    cima
    #
    cuni
    #
    cun
    #
    @51
    @1
    @12
    @47
    @59
    cun
    #
    cuni
    @61
    @1
    @11
    @62
    @1
    @11
    cS
    @46
    cD
    cun
    #
    cima
    @62
    @1
    @10
    @63
    cS
    @1
    @19
    @9
    cdif
    @46
    cD
    @9
    cdif
    #
    cun
    @10
    @63
    cC
    cD
    @9
    difundir
    @1
    cI
    @19
    @9
    @20
    difeq1d
    @1
    cD
    @64
    @46
    @1
    cD
    @9
    cin
    #
    c0
    wceq
    #
    cD
    @64
    wceq
    @1
    @65
    cD
    cC
    cin
    #
    wss
    #
    @67
    c0
    wceq
    @66
    @1
    @9
    cC
    wss
    @68
    @1
    cX
    cC
    wph
    @0
    simpr
    #
    snssd
    @9
    cC
    cD
    sslin
    syl
    @1
    @67
    cC
    cD
    cin
    #
    c0
    cC
    cD
    incom
    wph
    @70
    c0
    wceq
    @0
    dprdsplit.i
    adantr
    syl5eqr
    @65
    @67
    sseq0
    syl2anc
    cD
    @9
    disj3
    sylib
    uneq2d
    3eqtr4a
    imaeq2d
    cS
    @46
    cD
    imaundi
    syl6eq
    unieqd
    @47
    @59
    uniun
    syl6eq
    @1
    @61
    @49
    @38
    cun
    #
    @51
    @1
    @48
    @49
    wss
    @60
    @38
    wss
    @61
    @71
    wss
    @1
    @29
    @48
    cK
    @41
    @58
    dmdprdsplit2lem.k
    @1
    @48
    cS
    cC
    cima
    #
    cuni
    #
    @41
    @46
    cC
    wss
    #
    @47
    @72
    wss
    @48
    @73
    wss
    #
    cC
    @9
    difss
    #
    @46
    cC
    cS
    imass2
    @47
    @72
    uniss
    mp2b
    #
    @1
    @72
    @41
    cpw
    #
    wss
    @73
    @41
    wss
    @1
    @72
    cS
    crn
    #
    @78
    cS
    cC
    imassrn
    @1
    @79
    @29
    @78
    wph
    @79
    @29
    wss
    #
    @0
    wph
    cI
    @29
    cS
    wf
    #
    @80
    dprdsplit.2
    cI
    @29
    cS
    frn
    syl
    adantr
    @1
    @54
    @29
    @78
    wss
    @58
    @29
    @41
    mresspw
    syl
    sstrd
    #
    syl5ss
    @72
    @41
    sspwuni
    sylib
    #
    syl5ss
    #
    mrcssidd
    @1
    @60
    @60
    cK
    cfv
    #
    @38
    @1
    @29
    @60
    cK
    @41
    @58
    dmdprdsplit2lem.k
    @1
    @59
    @78
    wss
    @60
    @41
    wss
    @1
    @59
    @79
    @78
    cS
    cD
    imassrn
    @82
    syl5ss
    @59
    @41
    sspwuni
    sylib
    mrcssidd
    wph
    @38
    @85
    wceq
    @0
    wph
    @38
    @37
    crn
    #
    cuni
    #
    cK
    cfv
    #
    @85
    wph
    @44
    @38
    @88
    wceq
    dmdprdsplit2.2
    @37
    cG
    cK
    dmdprdsplit2lem.k
    dprdspan
    syl
    @60
    @87
    cK
    @59
    @86
    cS
    cD
    df-ima
    unieqi
    fveq2i
    syl6eqr
    adantr
    sseqtr4d
    @48
    @49
    @60
    @38
    unss12
    syl2anc
    @1
    @49
    @29
    wcel
    #
    @38
    @29
    wcel
    #
    @71
    @51
    wss
    @1
    @54
    @48
    @41
    wss
    @89
    @58
    @84
    @29
    @48
    cK
    @41
    dmdprdsplit2lem.k
    mrccl
    syl2anc
    #
    wph
    @90
    @0
    wph
    @44
    @90
    dmdprdsplit2.2
    @37
    cG
    dprdsubg
    syl
    adantr
    #
    @50
    @49
    @38
    cG
    @50
    eqid
    #
    lsmunss
    syl2anc
    sstrd
    eqsstrd
    @1
    @89
    @90
    @49
    @39
    wss
    @55
    @91
    @92
    @1
    @49
    @36
    @39
    @1
    @49
    @73
    cK
    cfv
    #
    @36
    @1
    @29
    @48
    cK
    @73
    @41
    @58
    dmdprdsplit2lem.k
    @75
    @1
    @77
    a1i
    @83
    mrcssd
    wph
    @36
    @94
    wceq
    @0
    wph
    @36
    @23
    crn
    #
    cuni
    #
    cK
    cfv
    #
    @94
    wph
    @27
    @36
    @97
    wceq
    dmdprdsplit2.1
    @23
    cG
    cK
    dmdprdsplit2lem.k
    dprdspan
    syl
    @73
    @96
    cK
    @72
    @95
    cS
    cC
    df-ima
    unieqi
    fveq2i
    syl6eqr
    adantr
    sseqtr4d
    #
    wph
    @40
    @0
    dmdprdsplit2.3
    adantr
    sstrd
    @50
    @49
    @38
    cG
    cZ
    @93
    dmdprdsplit.z
    lsmsubg
    syl3anc
    @29
    @12
    cK
    @51
    @41
    dmdprdsplit2lem.k
    mrcsscl
    syl3anc
    @13
    @51
    @4
    sslin
    syl
    @1
    @50
    @4
    @49
    @38
    cG
    c.0
    cZ
    @93
    wph
    @0
    cX
    cI
    wcel
    @4
    @29
    wcel
    #
    wph
    cC
    cI
    cX
    @30
    sselda
    wph
    cI
    @29
    cX
    cS
    dprdsplit.2
    ffvelrnda
    syldan
    #
    @91
    @92
    dmdprdsplit.0
    @1
    @4
    @49
    @50
    co
    #
    @38
    cin
    #
    @15
    @1
    @102
    @36
    @38
    cin
    #
    @15
    @1
    @101
    @36
    wss
    #
    @102
    @103
    wss
    @1
    @4
    @36
    wss
    #
    @49
    @36
    wss
    #
    @104
    @1
    @4
    @24
    @36
    @0
    @32
    wph
    @33
    adantl
    #
    @1
    @23
    cG
    cC
    cX
    wph
    @27
    @0
    dmdprdsplit2.1
    adantr
    #
    wph
    @28
    @0
    @31
    adantr
    #
    @69
    dprdub
    eqsstr3d
    @98
    @1
    @99
    @89
    @36
    @29
    wcel
    #
    @105
    @106
    wa
    @104
    wb
    @100
    @91
    wph
    @110
    @0
    wph
    @27
    @110
    dmdprdsplit2.1
    @23
    cG
    dprdsubg
    syl
    adantr
    @50
    @4
    @49
    @36
    cG
    @93
    lsmlub
    syl3anc
    mpbi2and
    @101
    @36
    @38
    ssrin
    syl
    wph
    @103
    @15
    wceq
    @0
    dmdprdsplit2.4
    adantr
    sseqtrd
    @1
    c.0
    @102
    @1
    @101
    @38
    c.0
    @1
    @4
    @101
    c.0
    @1
    @99
    @89
    @4
    @101
    wss
    @100
    @91
    @50
    @4
    @49
    cG
    @93
    lsmub1
    syl2anc
    @1
    @99
    c.0
    @4
    wcel
    @100
    @4
    cG
    c.0
    dmdprdsplit.0
    subg0cl
    syl
    sseldd
    @1
    @90
    c.0
    @38
    wcel
    @92
    @38
    cG
    c.0
    dmdprdsplit.0
    subg0cl
    syl
    elind
    snssd
    eqssd
    @1
    @24
    @23
    @46
    cima
    #
    cuni
    #
    cK
    cfv
    #
    cin
    @4
    @49
    cin
    @15
    @1
    @24
    @4
    @113
    @49
    @107
    @1
    @112
    @48
    cK
    @1
    @111
    @47
    @74
    @111
    @47
    wceq
    @1
    @76
    cS
    @46
    cC
    resima2
    mp1i
    unieqd
    fveq2d
    ineq12d
    @1
    @23
    cG
    cC
    cK
    cX
    c.0
    @108
    @109
    @69
    dmdprdsplit.0
    dmdprdsplit2lem.k
    dprddisj
    eqtr3d
    dmdprdsplit.z
    @1
    @49
    @4
    cG
    cZ
    dmdprdsplit.z
    @91
    @100
    @1
    @54
    @48
    @4
    cZ
    cfv
    #
    wss
    @114
    @29
    wcel
    #
    @49
    @114
    wss
    @58
    @1
    @48
    vy
    @46
    vy
    cv
    #
    cS
    cfv
    #
    ciun
    #
    @114
    @1
    @81
    cS
    wfun
    @118
    @48
    wceq
    wph
    @81
    @0
    dprdsplit.2
    adantr
    cI
    @29
    cS
    ffun
    vy
    @46
    cS
    funiunfv
    3syl
    @1
    @117
    @114
    wss
    #
    vy
    @46
    wral
    @118
    @114
    wss
    @1
    @119
    vy
    @46
    @1
    @116
    @46
    wcel
    #
    wa
    #
    @116
    @23
    cfv
    #
    @24
    cZ
    cfv
    @117
    @114
    @121
    @23
    cG
    cC
    @116
    cX
    cZ
    wph
    @27
    @0
    @120
    dmdprdsplit2.1
    ad2antrr
    wph
    @28
    @0
    @120
    @31
    ad2antrr
    @120
    @116
    cC
    wcel
    #
    @1
    @116
    cC
    @9
    eldifi
    adantl
    #
    wph
    @0
    @120
    simplr
    @120
    @116
    cX
    wne
    @1
    @116
    cC
    cX
    eldifsni
    adantl
    dmdprdsplit.z
    dprdcntz
    @121
    @123
    @122
    @117
    wceq
    @124
    @116
    cC
    cS
    fvres
    syl
    @121
    @24
    @4
    cZ
    @0
    @32
    wph
    @120
    @33
    ad2antlr
    fveq2d
    3sstr3d
    ralrimiva
    vy
    @46
    @117
    @114
    iunss
    sylibr
    eqsstr3d
    @1
    @56
    @4
    @41
    wss
    #
    @115
    @57
    @1
    @99
    @125
    @100
    @41
    @4
    cG
    @42
    subgss
    syl
    @41
    @4
    cG
    cZ
    @42
    dmdprdsplit.z
    cntzsubg
    syl2anc
    @29
    @48
    cK
    @114
    @41
    dmdprdsplit2lem.k
    mrcsscl
    syl3anc
    cntzrecd
    lsmdisj3
    sseqtrd
    jca
end
