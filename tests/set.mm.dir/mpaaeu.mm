include "caa.mm"
include "wcel.mm"
include "cv.mm"
include "cdgr.mm"
include "cfv.mm"
include "cdgraa.mm"
include "wceq.mm"
include "cc0.mm"
include "ccoe.mm"
include "c1.mm"
include "w3a.mm"
include "cq.mm"
include "cply.mm"
include "wrex.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "c0p.mm"
include "csn.mm"
include "cdif.mm"
include "cc.mm"
include "cdiv.mm"
include "co.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "wss.mm"
include "qsscn.mm"
include "wne.mm"
include "cn0.mm"
include "wf.mm"
include "eldifi.mm"
include "ad2antlr.mm"
include "cz.mm"
include "zssq.mm"
include "0z.mm"
include "sselii.mm"
include "eqid.mm"
include "coef2.mm"
include "sylancl.mm"
include "dgrcl.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "eldifsni.mm"
include "wb.mm"
include "dgreq0.mm"
include "necon3bid.mm"
include "mpbid.mm"
include "qreccl.mm"
include "syl2anc.mm"
include "plyconst.mm"
include "sylancr.mm"
include "simpl.mm"
include "simpr.mm"
include "caddc.mm"
include "qaddcl.mm"
include "adantl.mm"
include "qmulcl.mm"
include "plymul.mm"
include "coef3.mm"
include "reccld.mm"
include "recne0d.mm"
include "dgrmulc.mm"
include "syl3anc.mm"
include "simprl.mm"
include "eqtrd.mm"
include "aacn.mm"
include "ad2antrr.mm"
include "cvv.mm"
include "wfn.mm"
include "ovex.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "plyf.mm"
include "ffn.mm"
include "3syl.mm"
include "cnex.mm"
include "a1i.mm"
include "inidm.mm"
include "fvconst2.mm"
include "simplrr.mm"
include "ofval.mm"
include "mpdan.mm"
include "mul01d.mm"
include "coemulc.mm"
include "fveq1d.mm"
include "cn.mm"
include "dgraacl.mm"
include "nnnn0d.mm"
include "nn0ex.mm"
include "simplrl.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "recid2d.mm"
include "3eqtrd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "syl13anc.mm"
include "dgraalem.mm"
include "simprd.mm"
include "r19.29a.mm"
include "cmin.mm"
include "simp2.mm"
include "anim12i.mm"
include "sylan2.mm"
include "0m0e0.mm"
include "syl6eq.mm"
include "ex.mm"
include "com12.mm"
include "impl.mm"
include "clt.mm"
include "wbr.mm"
include "simpll.mm"
include "cneg.mm"
include "1z.mm"
include "zq.mm"
include "qnegcl.mm"
include "mp2b.mm"
include "plysub.mm"
include "simprr1.mm"
include "simprl1.mm"
include "eqtr4d.mm"
include "eqeltrd.mm"
include "simprl3.mm"
include "simprr3.mm"
include "3eqtr4d.mm"
include "dgrsub2.mm"
include "syl23anc.mm"
include "breqtrd.mm"
include "dgraa0p.mm"
include "df-0p.mm"
include "ofsubeq0.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "ralrimivva.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem mpaaeu
  let cA: class A
  let vp: setvar p
  let vd: setvar d
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cP: class P

  disjoint A p
  disjoint A d
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint d p
  disjoint a d
  disjoint b d
  disjoint c d
  disjoint a p
  disjoint b p
  disjoint c p
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint P d
  disjoint P p
  disjoint P a
  disjoint P b
  disjoint P c
  assert |- ( A e. AA -> E! p e. ( Poly ` QQ ) ( ( deg ` p ) = ( degAA ` A ) /\ ( p ` A ) = 0 /\ ( ( coeff ` p ) ` ( degAA ` A ) ) = 1 ) )

  proof
    cA
    caa
    wcel
    #
    vp
    cv
    #
    cdgr
    cfv
    #
    cA
    cdgraa
    cfv
    #
    wceq
    #
    cA
    @1
    cfv
    #
    cc0
    wceq
    #
    @3
    @1
    ccoe
    cfv
    #
    cfv
    #
    c1
    wceq
    #
    w3a
    #
    vp
    cq
    cply
    cfv
    #
    wrex
    #
    @10
    va
    cv
    #
    cdgr
    cfv
    #
    @3
    wceq
    #
    cA
    @13
    cfv
    #
    cc0
    wceq
    #
    @3
    @13
    ccoe
    cfv
    #
    cfv
    #
    c1
    wceq
    #
    w3a
    #
    wa
    #
    vp
    va
    weq
    #
    wi
    #
    va
    @11
    wral
    vp
    @11
    wral
    @10
    vp
    @11
    wreu
    @0
    @15
    @17
    wa
    #
    @12
    va
    @11
    c0p
    csn
    #
    cdif
    #
    @0
    @13
    @27
    wcel
    #
    wa
    #
    @25
    wa
    #
    cc
    c1
    @14
    @18
    cfv
    #
    cdiv
    co
    #
    csn
    #
    cxp
    #
    @13
    cmul
    cof
    #
    co
    #
    @11
    wcel
    #
    @36
    cdgr
    cfv
    #
    @3
    wceq
    #
    cA
    @36
    cfv
    #
    cc0
    wceq
    #
    @3
    @36
    ccoe
    cfv
    #
    cfv
    #
    c1
    wceq
    #
    @12
    @30
    @34
    @11
    wcel
    #
    @13
    @11
    wcel
    #
    @37
    @30
    cq
    cc
    wss
    @32
    cq
    wcel
    #
    @45
    qsscn
    @30
    @31
    cq
    wcel
    @31
    cc0
    wne
    #
    @47
    @30
    cn0
    cq
    @14
    @18
    @30
    @46
    cc0
    cq
    wcel
    cn0
    cq
    @18
    wf
    @28
    @46
    @0
    @25
    @13
    @11
    @26
    eldifi
    ad2antlr
    #
    cz
    cq
    cc0
    zssq
    0z
    sselii
    @18
    cq
    @13
    @18
    eqid
    #
    coef2
    sylancl
    @30
    @46
    @14
    cn0
    wcel
    @49
    cq
    @13
    dgrcl
    syl
    #
    ffvelrnd
    @30
    @13
    c0p
    wne
    #
    @48
    @28
    @52
    @0
    @25
    @13
    @11
    c0p
    eldifsni
    ad2antlr
    @30
    @46
    @52
    @48
    wb
    @49
    @46
    @13
    c0p
    @31
    cc0
    @18
    cq
    @13
    @14
    @14
    eqid
    @50
    dgreq0
    necon3bid
    syl
    mpbid
    #
    @31
    qreccl
    syl2anc
    @32
    cq
    plyconst
    sylancr
    @49
    @45
    @46
    wa
    #
    vb
    vc
    cq
    @34
    @13
    @45
    @46
    simpl
    @45
    @46
    simpr
    vb
    cv
    #
    cq
    wcel
    vc
    cv
    #
    cq
    wcel
    wa
    #
    @55
    @56
    caddc
    co
    cq
    wcel
    #
    @54
    @55
    @56
    qaddcl
    #
    adantl
    @57
    @55
    @56
    cmul
    co
    cq
    wcel
    #
    @54
    @55
    @56
    qmulcl
    #
    adantl
    plymul
    syl2anc
    @30
    @38
    @14
    @3
    @30
    @32
    cc
    wcel
    #
    @32
    cc0
    wne
    @46
    @38
    @14
    wceq
    @30
    @31
    @30
    cn0
    cc
    @14
    @18
    @30
    @46
    cn0
    cc
    @18
    wf
    #
    @49
    @18
    cq
    @13
    @50
    coef3
    syl
    #
    @51
    ffvelrnd
    #
    @53
    reccld
    #
    @30
    @31
    @65
    @53
    recne0d
    @49
    @32
    cq
    @13
    dgrmulc
    syl3anc
    @29
    @15
    @17
    simprl
    eqtrd
    @30
    @40
    @32
    cc0
    cmul
    co
    #
    cc0
    @30
    cA
    cc
    wcel
    #
    @40
    @67
    wceq
    @0
    @68
    @28
    @25
    cA
    aacn
    #
    ad2antrr
    @30
    cc
    cc
    @32
    cc0
    cmul
    cc
    @34
    @13
    cvv
    cvv
    cA
    @32
    cvv
    wcel
    #
    @34
    cc
    wfn
    @30
    c1
    @31
    cdiv
    ovex
    #
    cc
    @32
    cvv
    fnconstg
    mp1i
    @30
    @46
    cc
    cc
    @13
    wf
    #
    @13
    cc
    wfn
    #
    @49
    cq
    @13
    plyf
    #
    cc
    cc
    @13
    ffn
    #
    3syl
    cc
    cvv
    wcel
    #
    @30
    cnex
    a1i
    #
    @77
    cc
    inidm
    #
    @68
    cA
    @34
    cfv
    @32
    wceq
    @30
    cc
    @32
    cA
    @71
    fvconst2
    adantl
    @29
    @15
    @17
    @68
    simplrr
    ofval
    mpdan
    @30
    @32
    @66
    mul01d
    eqtrd
    @30
    @43
    @3
    cn0
    @33
    cxp
    #
    @18
    @35
    co
    #
    cfv
    #
    @32
    @31
    cmul
    co
    #
    c1
    @30
    @3
    @42
    @80
    @30
    @62
    @46
    @42
    @80
    wceq
    @66
    @49
    @32
    cq
    @13
    coemulc
    syl2anc
    fveq1d
    @30
    @3
    cn0
    wcel
    #
    @81
    @82
    wceq
    @30
    @3
    @0
    @3
    cn
    wcel
    #
    @28
    @25
    cA
    dgraacl
    #
    ad2antrr
    nnnn0d
    @30
    cn0
    cn0
    @32
    @31
    cmul
    cn0
    @79
    @18
    cvv
    cvv
    @3
    @70
    @79
    cn0
    wfn
    @30
    @71
    cn0
    @32
    cvv
    fnconstg
    mp1i
    @30
    @63
    @18
    cn0
    wfn
    @64
    cn0
    cc
    @18
    ffn
    syl
    cn0
    cvv
    wcel
    @30
    nn0ex
    a1i
    #
    @86
    cn0
    inidm
    @83
    @3
    @79
    cfv
    @32
    wceq
    @30
    cn0
    @32
    @3
    @71
    fvconst2
    adantl
    @30
    @83
    wa
    #
    @3
    @14
    @18
    @87
    @14
    @3
    @29
    @15
    @17
    @83
    simplrl
    eqcomd
    fveq2d
    ofval
    mpdan
    @30
    @31
    @65
    @53
    recid2d
    3eqtrd
    @10
    @39
    @41
    @44
    w3a
    vp
    @36
    @11
    @1
    @36
    wceq
    #
    @4
    @39
    @6
    @41
    @9
    @44
    @88
    @2
    @38
    @3
    @1
    @36
    cdgr
    fveq2
    eqeq1d
    @88
    @5
    @40
    cc0
    cA
    @1
    @36
    fveq1
    eqeq1d
    @88
    @8
    @43
    c1
    @88
    @3
    @7
    @42
    @1
    @36
    ccoe
    fveq2
    fveq1d
    eqeq1d
    3anbi123d
    rspcev
    syl13anc
    @0
    @84
    @25
    va
    @27
    wrex
    cA
    va
    dgraalem
    simprd
    r19.29a
    @0
    @24
    vp
    va
    @11
    @11
    @0
    @1
    @11
    wcel
    #
    @46
    wa
    #
    wa
    #
    @22
    @23
    @91
    @22
    wa
    #
    @1
    @13
    cmin
    cof
    co
    #
    cc
    cc0
    csn
    cxp
    #
    wceq
    #
    @23
    @92
    @93
    c0p
    @94
    @92
    cA
    @93
    cfv
    #
    cc0
    wceq
    #
    @93
    c0p
    wceq
    #
    @0
    @90
    @22
    @97
    @90
    @22
    wa
    @0
    @97
    @22
    @90
    @6
    @17
    wa
    #
    @0
    @97
    wi
    @10
    @6
    @21
    @17
    @4
    @6
    @9
    simp2
    @15
    @17
    @20
    simp2
    anim12i
    @90
    @99
    wa
    #
    @0
    @97
    @100
    @0
    wa
    @96
    cc0
    cc0
    cmin
    co
    #
    cc0
    @0
    @100
    @68
    @96
    @101
    wceq
    @69
    @100
    cc
    cc
    cc0
    cc0
    cmin
    cc
    @1
    @13
    cvv
    cvv
    cA
    @89
    @1
    cc
    wfn
    #
    @46
    @99
    @89
    cc
    cc
    @1
    wf
    #
    @102
    cq
    @1
    plyf
    #
    cc
    cc
    @1
    ffn
    syl
    ad2antrr
    @46
    @73
    @89
    @99
    @46
    @72
    @73
    @74
    @75
    syl
    ad2antlr
    @76
    @100
    cnex
    a1i
    #
    @105
    @78
    @90
    @6
    @17
    @68
    simplrl
    @90
    @6
    @17
    @68
    simplrr
    ofval
    sylan2
    0m0e0
    syl6eq
    ex
    sylan2
    com12
    impl
    @92
    @0
    @93
    @11
    wcel
    #
    @93
    cdgr
    cfv
    #
    @3
    clt
    wbr
    @97
    @98
    wb
    @0
    @90
    @22
    simpll
    @90
    @106
    @0
    @22
    @90
    vb
    vc
    cq
    @1
    @13
    @89
    @46
    simpl
    @89
    @46
    simpr
    @57
    @58
    @90
    @59
    adantl
    @57
    @60
    @90
    @61
    adantl
    c1
    cneg
    cq
    wcel
    #
    @90
    c1
    cz
    wcel
    c1
    cq
    wcel
    @108
    1z
    c1
    zq
    c1
    qnegcl
    mp2b
    a1i
    plysub
    ad2antlr
    @92
    @107
    @2
    @3
    clt
    @92
    @89
    @46
    @14
    @2
    wceq
    @2
    cn
    wcel
    @2
    @7
    cfv
    #
    @2
    @18
    cfv
    #
    wceq
    @107
    @2
    clt
    wbr
    @0
    @89
    @46
    @22
    simplrl
    @0
    @89
    @46
    @22
    simplrr
    @92
    @14
    @3
    @2
    @15
    @17
    @20
    @10
    @91
    simprr1
    @4
    @6
    @9
    @21
    @91
    simprl1
    #
    eqtr4d
    @92
    @2
    @3
    cn
    @111
    @0
    @84
    @90
    @22
    @85
    ad2antrr
    eqeltrd
    @92
    @8
    c1
    @109
    @110
    @4
    @6
    @9
    @21
    @91
    simprl3
    @92
    @2
    @3
    @7
    @111
    fveq2d
    @92
    @110
    @19
    c1
    @92
    @2
    @3
    @18
    @111
    fveq2d
    @15
    @17
    @20
    @10
    @91
    simprr3
    eqtrd
    3eqtr4d
    cq
    cq
    @1
    @13
    @2
    @2
    eqid
    dgrsub2
    syl23anc
    @111
    breqtrd
    cA
    @93
    dgraa0p
    syl3anc
    mpbid
    df-0p
    syl6eq
    @90
    @95
    @23
    wb
    #
    @0
    @22
    @89
    @103
    @72
    @112
    @46
    @104
    @74
    @76
    @103
    @72
    @112
    cnex
    cc
    @1
    @13
    cvv
    ofsubeq0
    mp3an1
    syl2an
    ad2antlr
    mpbid
    ex
    ralrimivva
    @10
    @21
    vp
    va
    @11
    @23
    @4
    @15
    @6
    @17
    @9
    @20
    @23
    @2
    @14
    @3
    @1
    @13
    cdgr
    fveq2
    eqeq1d
    @23
    @5
    @16
    cc0
    cA
    @1
    @13
    fveq1
    eqeq1d
    @23
    @8
    @19
    c1
    @23
    @3
    @7
    @18
    @1
    @13
    ccoe
    fveq2
    fveq1d
    eqeq1d
    3anbi123d
    reu4
    sylanbrc
end
