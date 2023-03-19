include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "ccnfld.mm"
include "crgspn.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cply.mm"
include "wrex.mm"
include "eleq2d.mm"
include "cab.mm"
include "cc.mm"
include "crg.mm"
include "cnring.mm"
include "a1i.mm"
include "cbs.mm"
include "cnfldbas.mm"
include "csubrg.mm"
include "wss.mm"
include "subrgss.mm"
include "syl.mm"
include "snssd.mm"
include "unssd.mm"
include "eqidd.mm"
include "caddc.mm"
include "cress.mm"
include "co.mm"
include "cmul.mm"
include "c1.mm"
include "cc0.mm"
include "c0g.mm"
include "cnfld0.mm"
include "cplusg.mm"
include "cnfldadd.mm"
include "wa.mm"
include "wf.mm"
include "plyf.mm"
include "ffvelrn.mm"
include "syl2anr.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "ss2abdv.mm"
include "abid2.mm"
include "eqtri.mm"
include "syl6sseq.mm"
include "cxp.mm"
include "plyconst.mm"
include "sylan.mm"
include "adantr.mm"
include "vex.mm"
include "fvconst2.mm"
include "eqcomd.mm"
include "fveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "syl5eqssr.mm"
include "csubg.mm"
include "subrgsubg.mm"
include "subg0cl.mm"
include "sseldd.mm"
include "w3a.mm"
include "biid.mm"
include "weq.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "elab.mm"
include "wi.mm"
include "cof.mm"
include "simplr.mm"
include "simpr.mm"
include "subrgacl.mm"
include "3expb.mm"
include "adantlr.mm"
include "plyadd.mm"
include "wfn.mm"
include "cvv.mm"
include "ffn.mm"
include "ad2antlr.mm"
include "adantl.mm"
include "cnex.mm"
include "ad2antrr.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "imbi2d.mm"
include "3imp.mm"
include "syl3anb.mm"
include "ovex.mm"
include "sylibr.mm"
include "cminusg.mm"
include "cneg.mm"
include "ax-1cn.mm"
include "cnfldneg.mm"
include "mp1i.mm"
include "cnfld1.mm"
include "subrg1cl.mm"
include "eqid.mm"
include "subginvcl.mm"
include "eqeltrrd.mm"
include "cnfldmul.mm"
include "subrgmcl.mm"
include "plymul.mm"
include "negex.mm"
include "fnconstg.mm"
include "oveq1d.mm"
include "mulm1d.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "fveq2.mm"
include "imp.mm"
include "sylan2b.mm"
include "fvex.mm"
include "cur.mm"
include "cmulr.mm"
include "issubrngd2.mm"
include "cidp.mm"
include "plyid.mm"
include "cid.mm"
include "cres.mm"
include "df-idp.mm"
include "fveq1i.mm"
include "fvresi.mm"
include "syl5req.mm"
include "wb.mm"
include "elabg.mm"
include "mpbird.mm"
include "rgspnmin.mm"
include "sseld.mm"
include "mpbiri.mm"
include "rexlimivw.mm"
include "elab3.mm"
include "syl6ib.mm"
include "rgspncl.mm"
include "rgspnssid.mm"
include "unssbd.mm"
include "snidg.mm"
include "unssad.mm"
include "cnsrplycl.mm"
include "impbid.mm"
include "bitrd.mm"

theorem rngunsnply
  let wph: wff ph
  let cB: class B
  let cS: class S
  let cV: class V
  let cX: class X
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  assume rngunsnply.b: |- ( ph -> B e. ( SubRing ` CCfld ) )
  assume rngunsnply.x: |- ( ph -> X e. CC )
  assume rngunsnply.s: |- ( ph -> S = ( ( RingSpan ` CCfld ) ` ( B u. { X } ) ) )

  disjoint p ph
  disjoint B p
  disjoint X p
  disjoint V p
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a p
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b p
  disjoint c d
  disjoint c e
  disjoint c p
  disjoint d e
  disjoint d p
  disjoint e p
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X e
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V d
  disjoint V e
  assert |- ( ph -> ( V e. S <-> E. p e. ( Poly ` B ) V = ( p ` X ) ) )

  proof
    wph
    cV
    cS
    wcel
    cV
    cB
    cX
    csn
    #
    cun
    #
    ccnfld
    crgspn
    cfv
    #
    cfv
    #
    wcel
    #
    cV
    cX
    vp
    cv
    #
    cfv
    #
    wceq
    #
    vp
    cB
    cply
    cfv
    #
    wrex
    #
    wph
    cS
    @3
    cV
    rngunsnply.s
    eleq2d
    wph
    @4
    @9
    wph
    @4
    cV
    va
    cv
    #
    @6
    wceq
    #
    vp
    @8
    wrex
    #
    va
    cab
    #
    wcel
    @9
    wph
    @3
    @13
    cV
    wph
    @1
    cc
    ccnfld
    @13
    @3
    @2
    ccnfld
    crg
    wcel
    wph
    cnring
    a1i
    #
    cc
    ccnfld
    cbs
    cfv
    #
    wceq
    wph
    cnfldbas
    a1i
    #
    wph
    cB
    @0
    cc
    wph
    cB
    ccnfld
    csubrg
    cfv
    #
    wcel
    #
    cB
    cc
    wss
    #
    rngunsnply.b
    cB
    cc
    ccnfld
    cnfldbas
    subrgss
    syl
    #
    wph
    cX
    cc
    rngunsnply.x
    snssd
    unssd
    #
    wph
    @2
    eqidd
    #
    wph
    @3
    eqidd
    #
    wph
    vb
    vc
    @13
    caddc
    ccnfld
    @13
    cress
    co
    #
    cmul
    c1
    ccnfld
    cc0
    wph
    @24
    eqidd
    cc0
    ccnfld
    c0g
    cfv
    wceq
    wph
    cnfld0
    a1i
    caddc
    ccnfld
    cplusg
    cfv
    wceq
    wph
    cnfldadd
    a1i
    wph
    @13
    @10
    cc
    wcel
    #
    va
    cab
    #
    @15
    wph
    @12
    @25
    va
    wph
    @11
    @25
    vp
    @8
    wph
    @5
    @8
    wcel
    #
    wa
    #
    @25
    @11
    @6
    cc
    wcel
    #
    @27
    cc
    cc
    @5
    wf
    cX
    cc
    wcel
    #
    @29
    wph
    cB
    @5
    plyf
    rngunsnply.x
    cc
    cc
    cX
    @5
    ffvelrn
    syl2anr
    @10
    @6
    cc
    eleq1
    syl5ibrcom
    rexlimdva
    ss2abdv
    @26
    cc
    @15
    va
    cc
    abid2
    cnfldbas
    eqtri
    syl6sseq
    wph
    cB
    @13
    cc0
    wph
    cB
    @10
    cB
    wcel
    #
    va
    cab
    @13
    va
    cB
    abid2
    wph
    @31
    @12
    va
    wph
    @31
    @12
    wph
    @31
    wa
    #
    cc
    @10
    csn
    cxp
    #
    @8
    wcel
    #
    @10
    cX
    @33
    cfv
    #
    wceq
    #
    @12
    wph
    @19
    @31
    @34
    @20
    @10
    cB
    plyconst
    sylan
    @32
    @35
    @10
    @32
    @30
    @35
    @10
    wceq
    wph
    @30
    @31
    rngunsnply.x
    adantr
    cc
    @10
    cX
    va
    vex
    fvconst2
    syl
    eqcomd
    @11
    @36
    vp
    @33
    @8
    @5
    @33
    wceq
    @6
    @35
    @10
    cX
    @5
    @33
    fveq1
    eqeq2d
    rspcev
    syl2anc
    ex
    ss2abdv
    syl5eqssr
    #
    wph
    cB
    ccnfld
    csubg
    cfv
    wcel
    #
    cc0
    cB
    wcel
    wph
    @18
    @38
    rngunsnply.b
    cB
    ccnfld
    subrgsubg
    syl
    #
    cB
    ccnfld
    cc0
    cnfld0
    subg0cl
    syl
    sseldd
    wph
    vb
    cv
    #
    @13
    wcel
    #
    vc
    cv
    #
    @13
    wcel
    #
    w3a
    #
    @40
    @42
    caddc
    co
    #
    @6
    wceq
    #
    vp
    @8
    wrex
    #
    @45
    @13
    wcel
    wph
    wph
    @41
    @40
    cX
    ve
    cv
    #
    cfv
    #
    wceq
    #
    ve
    @8
    wrex
    #
    @43
    @42
    cX
    vd
    cv
    #
    cfv
    #
    wceq
    #
    vd
    @8
    wrex
    #
    @47
    wph
    biid
    #
    @12
    @51
    va
    @40
    vb
    vex
    va
    vb
    weq
    #
    @12
    @40
    @6
    wceq
    #
    vp
    @8
    wrex
    @51
    @57
    @11
    @58
    vp
    @8
    @10
    @40
    @6
    eqeq1
    rexbidv
    @58
    @50
    vp
    ve
    @8
    vp
    ve
    weq
    @6
    @49
    @40
    cX
    @5
    @48
    fveq1
    eqeq2d
    cbvrexv
    syl6bb
    elab
    #
    @12
    @55
    va
    @42
    vc
    vex
    va
    vc
    weq
    #
    @12
    @42
    @6
    wceq
    #
    vp
    @8
    wrex
    @55
    @60
    @11
    @61
    vp
    @8
    @10
    @42
    @6
    eqeq1
    rexbidv
    @61
    @54
    vp
    vd
    @8
    vp
    vd
    weq
    @6
    @53
    @42
    cX
    @5
    @52
    fveq1
    eqeq2d
    cbvrexv
    syl6bb
    elab
    #
    wph
    @51
    @55
    @47
    wph
    @50
    @55
    @47
    wi
    #
    ve
    @8
    wph
    @48
    @8
    wcel
    #
    wa
    #
    @63
    @50
    @55
    @49
    @42
    caddc
    co
    #
    @6
    wceq
    #
    vp
    @8
    wrex
    #
    wi
    @65
    @54
    @68
    vd
    @8
    @65
    @52
    @8
    wcel
    #
    wa
    #
    @68
    @54
    @49
    @53
    caddc
    co
    #
    @6
    wceq
    #
    vp
    @8
    wrex
    #
    @70
    @48
    @52
    caddc
    cof
    co
    #
    @8
    wcel
    @71
    cX
    @74
    cfv
    #
    wceq
    #
    @73
    @70
    va
    vb
    cB
    @48
    @52
    wph
    @64
    @69
    simplr
    #
    @65
    @69
    simpr
    #
    @65
    @31
    @40
    cB
    wcel
    #
    wa
    #
    @10
    @40
    caddc
    co
    cB
    wcel
    #
    @69
    wph
    @80
    @81
    @64
    wph
    @18
    @80
    @81
    rngunsnply.b
    @18
    @31
    @79
    @81
    cB
    caddc
    ccnfld
    @10
    @40
    cnfldadd
    subrgacl
    3expb
    sylan
    adantlr
    #
    adantlr
    #
    plyadd
    @70
    @75
    @71
    @70
    @48
    cc
    wfn
    #
    @52
    cc
    wfn
    #
    cc
    cvv
    wcel
    #
    @30
    @75
    @71
    wceq
    @64
    @84
    wph
    @69
    @64
    cc
    cc
    @48
    wf
    #
    @84
    cB
    @48
    plyf
    #
    cc
    cc
    @48
    ffn
    syl
    #
    ad2antlr
    #
    @69
    @85
    @65
    @69
    cc
    cc
    @52
    wf
    @85
    cB
    @52
    plyf
    cc
    cc
    @52
    ffn
    syl
    adantl
    #
    @86
    @70
    cnex
    a1i
    #
    wph
    @30
    @64
    @69
    rngunsnply.x
    ad2antrr
    #
    cc
    caddc
    @48
    @52
    cvv
    cX
    fnfvof
    syl22anc
    eqcomd
    @72
    @76
    vp
    @74
    @8
    @5
    @74
    wceq
    @6
    @75
    @71
    cX
    @5
    @74
    fveq1
    eqeq2d
    rspcev
    syl2anc
    @54
    @67
    @72
    vp
    @8
    @54
    @66
    @71
    @6
    @42
    @53
    @49
    caddc
    oveq2
    eqeq1d
    rexbidv
    syl5ibrcom
    rexlimdva
    @50
    @47
    @68
    @55
    @50
    @46
    @67
    vp
    @8
    @50
    @45
    @66
    @6
    @40
    @49
    @42
    caddc
    oveq1
    eqeq1d
    rexbidv
    imbi2d
    syl5ibrcom
    rexlimdva
    3imp
    syl3anb
    @12
    @47
    va
    @45
    @40
    @42
    caddc
    ovex
    @10
    @45
    wceq
    @11
    @46
    vp
    @8
    @10
    @45
    @6
    eqeq1
    rexbidv
    elab
    sylibr
    wph
    @41
    wa
    @40
    ccnfld
    cminusg
    cfv
    #
    cfv
    #
    @6
    wceq
    #
    vp
    @8
    wrex
    #
    @95
    @13
    wcel
    @41
    wph
    @51
    @97
    @59
    wph
    @51
    @97
    wph
    @50
    @97
    ve
    @8
    @65
    @97
    @50
    @49
    @94
    cfv
    #
    @6
    wceq
    #
    vp
    @8
    wrex
    #
    @65
    cc
    c1
    cneg
    #
    csn
    cxp
    #
    @48
    cmul
    cof
    #
    co
    #
    @8
    wcel
    @98
    cX
    @104
    cfv
    #
    wceq
    #
    @100
    @65
    va
    vb
    cB
    @102
    @48
    wph
    @102
    @8
    wcel
    #
    @64
    wph
    @19
    @101
    cB
    wcel
    @107
    @20
    wph
    c1
    @94
    cfv
    #
    @101
    cB
    c1
    cc
    wcel
    @108
    @101
    wceq
    wph
    ax-1cn
    c1
    cnfldneg
    mp1i
    wph
    @38
    c1
    cB
    wcel
    #
    @108
    cB
    wcel
    @39
    wph
    @18
    @109
    rngunsnply.b
    cB
    ccnfld
    c1
    cnfld1
    subrg1cl
    syl
    #
    cB
    ccnfld
    @94
    c1
    @94
    eqid
    subginvcl
    syl2anc
    eqeltrrd
    @101
    cB
    plyconst
    syl2anc
    adantr
    wph
    @64
    simpr
    @82
    wph
    @80
    @10
    @40
    cmul
    co
    cB
    wcel
    #
    @64
    wph
    @18
    @80
    @111
    rngunsnply.b
    @18
    @31
    @79
    @111
    cB
    ccnfld
    cmul
    @10
    @40
    cnfldmul
    subrgmcl
    3expb
    sylan
    adantlr
    #
    plymul
    @65
    @98
    @49
    cneg
    #
    @105
    @65
    @49
    cc
    wcel
    #
    @98
    @113
    wceq
    @64
    @87
    @30
    @114
    wph
    @88
    rngunsnply.x
    cc
    cc
    cX
    @48
    ffvelrn
    syl2anr
    #
    @49
    cnfldneg
    syl
    @65
    @105
    cX
    @102
    cfv
    #
    @49
    cmul
    co
    #
    @101
    @49
    cmul
    co
    @113
    @65
    @102
    cc
    wfn
    #
    @84
    @86
    @30
    @105
    @117
    wceq
    @101
    cvv
    wcel
    @118
    @65
    c1
    negex
    #
    cc
    @101
    cvv
    fnconstg
    mp1i
    @64
    @84
    wph
    @89
    adantl
    @86
    @65
    cnex
    a1i
    wph
    @30
    @64
    rngunsnply.x
    adantr
    #
    cc
    cmul
    @102
    @48
    cvv
    cX
    fnfvof
    syl22anc
    @65
    @116
    @101
    @49
    cmul
    @65
    @30
    @116
    @101
    wceq
    @120
    cc
    @101
    cX
    @119
    fvconst2
    syl
    oveq1d
    @65
    @49
    @115
    mulm1d
    3eqtrd
    eqtr4d
    @99
    @106
    vp
    @104
    @8
    @5
    @104
    wceq
    @6
    @105
    @98
    cX
    @5
    @104
    fveq1
    eqeq2d
    rspcev
    syl2anc
    @50
    @96
    @99
    vp
    @8
    @50
    @95
    @98
    @6
    @40
    @49
    @94
    fveq2
    eqeq1d
    rexbidv
    syl5ibrcom
    rexlimdva
    imp
    sylan2b
    @12
    @97
    va
    @95
    @40
    @94
    fvex
    @10
    @95
    wceq
    @11
    @96
    vp
    @8
    @10
    @95
    @6
    eqeq1
    rexbidv
    elab
    sylibr
    c1
    ccnfld
    cur
    cfv
    wceq
    wph
    cnfld1
    a1i
    cmul
    ccnfld
    cmulr
    cfv
    wceq
    wph
    cnfldmul
    a1i
    wph
    cB
    @13
    c1
    @37
    @110
    sseldd
    @44
    @40
    @42
    cmul
    co
    #
    @6
    wceq
    #
    vp
    @8
    wrex
    #
    @121
    @13
    wcel
    wph
    wph
    @41
    @51
    @43
    @55
    @123
    @56
    @59
    @62
    wph
    @51
    @55
    @123
    wph
    @50
    @55
    @123
    wi
    #
    ve
    @8
    @65
    @124
    @50
    @55
    @49
    @42
    cmul
    co
    #
    @6
    wceq
    #
    vp
    @8
    wrex
    #
    wi
    @65
    @54
    @127
    vd
    @8
    @70
    @127
    @54
    @49
    @53
    cmul
    co
    #
    @6
    wceq
    #
    vp
    @8
    wrex
    #
    @70
    @48
    @52
    @103
    co
    #
    @8
    wcel
    @128
    cX
    @131
    cfv
    #
    wceq
    #
    @130
    @70
    va
    vb
    cB
    @48
    @52
    @77
    @78
    @83
    @65
    @80
    @111
    @69
    @112
    adantlr
    plymul
    @70
    @132
    @128
    @70
    @84
    @85
    @86
    @30
    @132
    @128
    wceq
    @90
    @91
    @92
    @93
    cc
    cmul
    @48
    @52
    cvv
    cX
    fnfvof
    syl22anc
    eqcomd
    @129
    @133
    vp
    @131
    @8
    @5
    @131
    wceq
    @6
    @132
    @128
    cX
    @5
    @131
    fveq1
    eqeq2d
    rspcev
    syl2anc
    @54
    @126
    @129
    vp
    @8
    @54
    @125
    @128
    @6
    @42
    @53
    @49
    cmul
    oveq2
    eqeq1d
    rexbidv
    syl5ibrcom
    rexlimdva
    @50
    @123
    @127
    @55
    @50
    @122
    @126
    vp
    @8
    @50
    @121
    @125
    @6
    @40
    @49
    @42
    cmul
    oveq1
    eqeq1d
    rexbidv
    imbi2d
    syl5ibrcom
    rexlimdva
    3imp
    syl3anb
    @12
    @123
    va
    @121
    @40
    @42
    cmul
    ovex
    @10
    @121
    wceq
    @11
    @122
    vp
    @8
    @10
    @121
    @6
    eqeq1
    rexbidv
    elab
    sylibr
    @14
    issubrngd2
    wph
    cB
    @0
    @13
    @37
    wph
    cX
    @13
    wph
    cX
    @13
    wcel
    #
    cX
    @6
    wceq
    #
    vp
    @8
    wrex
    #
    wph
    cidp
    @8
    wcel
    #
    cX
    cX
    cidp
    cfv
    #
    wceq
    #
    @136
    wph
    @19
    @109
    @137
    @20
    @110
    cB
    plyid
    syl2anc
    wph
    @138
    cX
    cid
    cc
    cres
    #
    cfv
    #
    cX
    cX
    cidp
    @140
    df-idp
    fveq1i
    wph
    @30
    @141
    cX
    wceq
    rngunsnply.x
    cc
    cX
    fvresi
    syl
    syl5req
    @135
    @139
    vp
    cidp
    @8
    @5
    cidp
    wceq
    @6
    @138
    cX
    cX
    @5
    cidp
    fveq1
    eqeq2d
    rspcev
    syl2anc
    wph
    @30
    @134
    @136
    wb
    rngunsnply.x
    @12
    @136
    va
    cX
    cc
    @10
    cX
    wceq
    @11
    @135
    vp
    @8
    @10
    cX
    @6
    eqeq1
    rexbidv
    elabg
    syl
    mpbird
    snssd
    unssd
    rgspnmin
    sseld
    @12
    @9
    va
    cV
    @7
    cV
    cvv
    wcel
    #
    vp
    @8
    @7
    @142
    @6
    cvv
    wcel
    cX
    @5
    fvex
    cV
    @6
    cvv
    eleq1
    mpbiri
    rexlimivw
    @10
    cV
    wceq
    @11
    @7
    vp
    @8
    @10
    cV
    @6
    eqeq1
    rexbidv
    elab3
    syl6ib
    wph
    @7
    @4
    vp
    @8
    @28
    @4
    @7
    @6
    @3
    wcel
    @28
    cB
    @5
    @3
    cX
    wph
    @3
    @17
    wcel
    @27
    wph
    @1
    cc
    ccnfld
    @3
    @2
    @14
    @16
    @21
    @22
    @23
    rgspncl
    adantr
    wph
    @27
    simpr
    wph
    cX
    @3
    wcel
    @27
    wph
    @0
    @3
    cX
    wph
    cB
    @0
    @3
    wph
    @1
    cc
    ccnfld
    @3
    @2
    @14
    @16
    @21
    @22
    @23
    rgspnssid
    #
    unssbd
    wph
    @30
    cX
    @0
    wcel
    rngunsnply.x
    cX
    cc
    snidg
    syl
    sseldd
    adantr
    wph
    cB
    @3
    wss
    @27
    wph
    cB
    @0
    @3
    @143
    unssad
    adantr
    cnsrplycl
    cV
    @6
    @3
    eleq1
    syl5ibrcom
    rexlimdva
    impbid
    bitrd
end
