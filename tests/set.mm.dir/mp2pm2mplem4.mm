include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cn0.mm"
include "wa.mm"
include "cfv.mm"
include "cdecpmat.mm"
include "co.mm"
include "cv.mm"
include "cco1.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "mp2pm2mplem3.mm"
include "clt.mm"
include "wbr.mm"
include "c0g.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cc0.mm"
include "cfz.mm"
include "cif.mm"
include "cbs.mm"
include "eqid.mm"
include "ccmn.mm"
include "ply1ring.mm"
include "3ad2ant2.mm"
include "ringcmn.mm"
include "syl.mm"
include "ad3antrrr.mm"
include "3ad2ant1.mm"
include "simpl2.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "simpl3.mm"
include "coe1fvalcl.mm"
include "sylan.mm"
include "matecld.mm"
include "simpr.mm"
include "cmgp.mm"
include "ply1tmcl.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "simp1lr.mm"
include "oveq.mm"
include "oveq1d.mm"
include "csca.mm"
include "cvv.mm"
include "3simpa.mm"
include "mat0op.mm"
include "weq.mm"
include "eqidd.mm"
include "simprl.mm"
include "simprr.mm"
include "fvexd.mm"
include "ovmpt2d.mm"
include "ply1sca.mm"
include "fveq2d.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "ad4antr.mm"
include "ply1moncl.mm"
include "syl2anc.mm"
include "lmod0vs.mm"
include "3eqtrd.mm"
include "sylan9eqr.mm"
include "exp31.mm"
include "a2d.mm"
include "ralimdva.mm"
include "impancom.mm"
include "3impib.mm"
include "breq2.mm"
include "fveq2.mm"
include "oveqd.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "sylibr.mm"
include "gsummptnn0fzv.mm"
include "fveq1d.mm"
include "simpllr.mm"
include "expcom.mm"
include "elfznn0.mm"
include "syl11.mm"
include "ralrimiv.mm"
include "fzfid.mm"
include "coe1fzgsumd.mm"
include "eqtrd.mm"
include "mpt2eq3dva.mm"
include "syl2an.mm"
include "adantl.mm"
include "coe1tm.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "simpl1r.mm"
include "ovex.mm"
include "fvex.mm"
include "ifex.mm"
include "a1i.mm"
include "fvmptd.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "rspcva.mm"
include "eqcomd.mm"
include "3adant3.mm"
include "ad3antlr.mm"
include "wn.mm"
include "cle.mm"
include "elfz2nn0.mm"
include "cr.mm"
include "nn0re.mm"
include "ad2antlr.mm"
include "lelttr.mm"
include "wo.mm"
include "olcd.mm"
include "wne.mm"
include "df-ne.mm"
include "wb.mm"
include "lttri2.mm"
include "syl2anr.mm"
include "syl5bbr.mm"
include "mpbird.mm"
include "ex.mm"
include "syld.mm"
include "exp4b.mm"
include "com24.mm"
include "expimpd.mm"
include "com23.mm"
include "imp.mm"
include "3adant2.mm"
include "sylbi.mm"
include "com13.mm"
include "iffalsed.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "gsumz.mm"
include "sylancl.mm"
include "3eqtr4d.mm"
include "expr.mm"
include "com14.mm"
include "com25.mm"
include "pm2.43i.mm"
include "impcom.mm"
include "imp31.mm"
include "com12.mm"
include "csb.mm"
include "ovexd.mm"
include "lenlt.mm"
include "simpll.mm"
include "simplr.mm"
include "syl3anbrc.mm"
include "sylbird.mm"
include "adantll.mm"
include "eqcom.mm"
include "ifbi.mm"
include "ax-mp.mm"
include "mpteq2i.mm"
include "sylan2.mm"
include "gsummpt1n0.mm"
include "csbov.mm"
include "csbfv.mm"
include "syl5eq.mm"
include "mpt2eq3dv.mm"
include "oveq12.mm"
include "ralrimivva.mm"
include "simpl1.mm"
include "oveqi.mm"
include "eqtri.mm"
include "simp2.mm"
include "simp3.mm"
include "3ad2antl3.mm"
include "syl5eqel.mm"
include "matbas2d.mm"
include "eqmat.mm"
include "pm2.61i.mm"
include "cfsupp.mm"
include "wrex.mm"
include "coe1sfi.mm"
include "cmap.mm"
include "crab.mm"
include "coe1fsupp.mm"
include "elrabi.mm"
include "3syl.mm"
include "fsuppmapnn0ub.mm"
include "mpd.mm"
include "r19.29a.mm"

theorem mp2pm2mplem4
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let cI: class I
  let cK: class K
  let cL: class L
  let cN: class N
  let cO: class O
  let cY: class Y
  let vp: setvar p
  let vs: setvar s
  let vx: setvar x
  let vl: setvar l
  let va: setvar a
  let vb: setvar b
  assume mp2pm2mp.a: |- A = ( N Mat R )
  assume mp2pm2mp.q: |- Q = ( Poly1 ` A )
  assume mp2pm2mp.l: |- L = ( Base ` Q )
  assume mp2pm2mp.m: |- .x. = ( .s ` P )
  assume mp2pm2mp.e: |- E = ( .g ` ( mulGrp ` P ) )
  assume mp2pm2mp.y: |- Y = ( var1 ` R )
  assume mp2pm2mp.i: |- I = ( p e. L |-> ( i e. N , j e. N |-> ( P gsum ( k e. NN0 |-> ( ( i ( ( coe1 ` p ) ` k ) j ) .x. ( k E Y ) ) ) ) ) )
  assume mp2pm2mplem2.p: |- P = ( Poly1 ` R )

  disjoint A i
  disjoint A j
  disjoint A k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint E k
  disjoint K k
  disjoint Y k
  disjoint E p
  disjoint L p
  disjoint N i
  disjoint N j
  disjoint N p
  disjoint i j
  disjoint i p
  disjoint j p
  disjoint O i
  disjoint O j
  disjoint O p
  disjoint O k
  disjoint k p
  disjoint P p
  disjoint R p
  disjoint Y p
  disjoint .x. p
  disjoint L k
  disjoint P i
  disjoint P j
  disjoint P k
  disjoint i k
  disjoint j k
  disjoint R k
  disjoint .x. k
  disjoint E i
  disjoint E j
  disjoint K i
  disjoint K j
  disjoint L i
  disjoint L j
  disjoint N k
  disjoint R i
  disjoint R j
  disjoint Y i
  disjoint Y j
  disjoint .x. i
  disjoint .x. j
  disjoint A s
  disjoint A x
  disjoint i s
  disjoint i x
  disjoint j s
  disjoint j x
  disjoint k s
  disjoint k x
  disjoint s x
  disjoint E s
  disjoint E x
  disjoint E l
  disjoint K s
  disjoint K x
  disjoint K l
  disjoint L l
  disjoint L s
  disjoint L x
  disjoint N l
  disjoint N s
  disjoint l s
  disjoint N x
  disjoint O l
  disjoint O s
  disjoint O x
  disjoint P l
  disjoint P s
  disjoint P x
  disjoint R l
  disjoint R s
  disjoint R x
  disjoint Y l
  disjoint Y s
  disjoint Y x
  disjoint .x. l
  disjoint .x. s
  disjoint .x. x
  disjoint a b
  disjoint a s
  disjoint b s
  disjoint i l
  disjoint j l
  disjoint k l
  disjoint K a
  disjoint K b
  disjoint a b
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint L a
  disjoint L b
  disjoint N a
  disjoint N b
  disjoint a k
  disjoint b k
  disjoint O a
  disjoint O b
  disjoint R a
  disjoint R b
  assert |- ( ( ( N e. Fin /\ R e. Ring /\ O e. L ) /\ K e. NN0 ) -> ( ( I ` O ) decompPMat K ) = ( ( coe1 ` O ) ` K ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cO
    cL
    wcel
    #
    w3a
    #
    cK
    cn0
    wcel
    #
    wa
    #
    cO
    cI
    cfv
    cK
    cdecpmat
    co
    vi
    vj
    cN
    cN
    cK
    cP
    vk
    cn0
    vi
    cv
    #
    vj
    cv
    #
    vk
    cv
    #
    cO
    cco1
    cfv
    #
    cfv
    #
    co
    #
    @8
    cY
    cE
    co
    #
    c.x
    co
    #
    cmpt
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    cK
    @9
    cfv
    #
    cA
    cP
    cQ
    cR
    c.x
    vi
    vj
    vk
    cE
    cI
    cK
    cL
    cN
    cO
    cY
    vp
    mp2pm2mp.a
    mp2pm2mp.q
    mp2pm2mp.l
    mp2pm2mp.m
    mp2pm2mp.e
    mp2pm2mp.y
    mp2pm2mp.i
    mp2pm2mplem2.p
    mp2pm2mplem3
    @5
    vs
    cv
    #
    vx
    cv
    #
    clt
    wbr
    #
    @20
    @9
    cfv
    #
    cA
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    @17
    @18
    wceq
    vs
    cn0
    @5
    @19
    cn0
    wcel
    #
    wa
    #
    @26
    wa
    #
    @17
    vi
    vj
    cN
    cN
    cR
    vk
    cc0
    @19
    cfz
    co
    #
    cK
    @13
    cco1
    cfv
    #
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    vi
    vj
    cN
    cN
    cR
    vk
    @30
    cK
    @8
    wceq
    #
    @11
    cR
    c0g
    cfv
    #
    cif
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    @18
    @29
    vi
    vj
    cN
    cN
    @16
    @34
    @29
    @6
    cN
    wcel
    #
    @7
    cN
    wcel
    #
    w3a
    #
    @16
    cK
    cP
    vk
    @30
    @13
    cmpt
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    @34
    @44
    cK
    @15
    @46
    @44
    @14
    @45
    cco1
    @44
    cP
    cbs
    cfv
    #
    @13
    @19
    vk
    cP
    cP
    c0g
    cfv
    #
    @47
    eqid
    #
    @48
    eqid
    #
    @29
    @42
    cP
    ccmn
    wcel
    #
    @43
    @3
    @51
    @4
    @27
    @26
    @3
    cP
    crg
    wcel
    #
    @51
    @1
    @0
    @52
    @2
    cP
    cR
    mp2pm2mplem2.p
    ply1ring
    3ad2ant2
    cP
    ringcmn
    syl
    ad3antrrr
    3ad2ant1
    @44
    @13
    @47
    wcel
    #
    vk
    cn0
    @44
    @8
    cn0
    wcel
    #
    wa
    #
    @1
    @11
    cR
    cbs
    cfv
    #
    wcel
    #
    @54
    @53
    @44
    @1
    @54
    @29
    @42
    @1
    @43
    @5
    @1
    @27
    @26
    @0
    @1
    @2
    @4
    simpl2
    #
    ad2antrr
    3ad2ant1
    #
    adantr
    @55
    cA
    cA
    cbs
    cfv
    #
    cR
    @6
    @7
    @56
    @10
    cN
    mp2pm2mp.a
    @56
    eqid
    #
    @60
    eqid
    #
    @29
    @42
    @43
    @54
    simpl2
    @29
    @42
    @43
    @54
    simpl3
    @44
    @2
    @54
    @10
    @60
    wcel
    #
    @29
    @42
    @2
    @43
    @5
    @2
    @27
    @26
    @0
    @1
    @2
    @4
    simpl3
    #
    ad2antrr
    #
    3ad2ant1
    @9
    cL
    cQ
    cA
    cO
    @60
    @8
    @9
    eqid
    #
    mp2pm2mp.l
    mp2pm2mp.q
    @62
    coe1fvalcl
    #
    sylan
    matecld
    @44
    @54
    simpr
    @47
    @11
    @8
    cP
    cR
    c.x
    cE
    @56
    cP
    cmgp
    cfv
    #
    cY
    @61
    mp2pm2mplem2.p
    mp2pm2mp.y
    mp2pm2mp.m
    @68
    eqid
    #
    mp2pm2mp.e
    @49
    ply1tmcl
    syl3anc
    #
    ralrimiva
    @5
    @27
    @26
    @42
    @43
    simp1lr
    @44
    @21
    @6
    @7
    @22
    co
    #
    @20
    cY
    cE
    co
    #
    c.x
    co
    #
    @48
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    @19
    @8
    clt
    wbr
    #
    @13
    @48
    wceq
    #
    wi
    #
    vk
    cn0
    wral
    @29
    @42
    @43
    @76
    @28
    @42
    @43
    wa
    #
    @26
    @76
    @28
    @80
    wa
    #
    @25
    @75
    vx
    cn0
    @81
    @20
    cn0
    wcel
    #
    wa
    #
    @21
    @24
    @74
    @83
    @21
    @24
    @74
    @24
    @83
    @21
    wa
    @73
    @6
    @7
    @23
    co
    #
    @72
    c.x
    co
    #
    @48
    @24
    @71
    @84
    @72
    c.x
    @6
    @7
    @22
    @23
    oveq
    oveq1d
    @83
    @85
    @48
    wceq
    @21
    @83
    @85
    @37
    @72
    c.x
    co
    cP
    csca
    cfv
    #
    c0g
    cfv
    #
    @72
    c.x
    co
    #
    @48
    @83
    @84
    @37
    @72
    c.x
    @81
    @84
    @37
    wceq
    @82
    @81
    va
    vb
    @6
    @7
    cN
    cN
    @37
    @37
    @23
    cvv
    @81
    @0
    @1
    wa
    #
    @23
    va
    vb
    cN
    cN
    @37
    cmpt2
    wceq
    @3
    @89
    @4
    @27
    @80
    @0
    @1
    @2
    3simpa
    ad3antrrr
    cA
    cR
    va
    vb
    cN
    @37
    mp2pm2mp.a
    @37
    eqid
    #
    mat0op
    syl
    @81
    va
    vi
    weq
    vb
    vj
    weq
    wa
    wa
    @37
    eqidd
    @28
    @42
    @43
    simprl
    @28
    @42
    @43
    simprr
    @81
    cR
    c0g
    fvexd
    ovmpt2d
    adantr
    oveq1d
    @83
    @37
    @87
    @72
    c.x
    @83
    cR
    @86
    c0g
    @83
    @1
    cR
    @86
    wceq
    @5
    @1
    @27
    @80
    @82
    @58
    ad3antrrr
    #
    cP
    cR
    crg
    mp2pm2mplem2.p
    ply1sca
    syl
    fveq2d
    oveq1d
    @83
    cP
    clmod
    wcel
    #
    @72
    @47
    wcel
    #
    @88
    @48
    wceq
    @3
    @92
    @4
    @27
    @80
    @82
    @1
    @0
    @92
    @2
    cP
    cR
    mp2pm2mplem2.p
    ply1lmod
    3ad2ant2
    ad4antr
    @83
    @1
    @82
    @93
    @91
    @81
    @82
    simpr
    @47
    @20
    cP
    cR
    cE
    @68
    cY
    mp2pm2mplem2.p
    mp2pm2mp.y
    @69
    mp2pm2mp.e
    @49
    ply1moncl
    syl2anc
    c.x
    @86
    @87
    @47
    cP
    @72
    @48
    @49
    @86
    eqid
    mp2pm2mp.m
    @87
    eqid
    @50
    lmod0vs
    syl2anc
    3eqtrd
    adantr
    sylan9eqr
    exp31
    a2d
    ralimdva
    impancom
    3impib
    @79
    @75
    vk
    vx
    cn0
    vk
    vx
    weq
    #
    @77
    @21
    @78
    @74
    @8
    @20
    @19
    clt
    breq2
    @94
    @13
    @73
    @48
    @94
    @11
    @71
    @12
    @72
    c.x
    @94
    @10
    @22
    @6
    @7
    @8
    @20
    @9
    fveq2
    oveqd
    @8
    @20
    cY
    cE
    oveq1
    oveq12d
    eqeq1d
    imbi12d
    cbvralv
    sylibr
    gsummptnn0fzv
    fveq2d
    fveq1d
    @44
    vk
    @47
    cP
    cR
    cK
    @13
    @30
    mp2pm2mplem2.p
    @49
    @59
    @29
    @42
    @4
    @43
    @3
    @4
    @27
    @26
    simpllr
    3ad2ant1
    @44
    @53
    vk
    @30
    @54
    @44
    @53
    @8
    @30
    wcel
    #
    @44
    @54
    @53
    @70
    expcom
    @8
    @19
    elfznn0
    #
    syl11
    ralrimiv
    @44
    cc0
    @19
    fzfid
    coe1fzgsumd
    eqtrd
    mpt2eq3dva
    @5
    @35
    @41
    wceq
    @27
    @26
    @5
    vi
    vj
    cN
    cN
    @34
    @40
    @5
    @42
    @43
    w3a
    #
    @33
    @39
    cR
    cgsu
    @97
    vk
    @30
    @32
    @38
    @97
    @95
    wa
    #
    vl
    cK
    vl
    vk
    weq
    #
    @11
    @37
    cif
    #
    @38
    cn0
    @31
    cvv
    @98
    @1
    @57
    @54
    @31
    vl
    cn0
    @100
    cmpt
    wceq
    @97
    @1
    @95
    @5
    @42
    @1
    @43
    @58
    3ad2ant1
    adantr
    @98
    cA
    @60
    cR
    @6
    @7
    @56
    @10
    cN
    mp2pm2mp.a
    @61
    @62
    @5
    @42
    @43
    @95
    simpl2
    @5
    @42
    @43
    @95
    simpl3
    @97
    @2
    @54
    @63
    @95
    @5
    @42
    @2
    @43
    @64
    3ad2ant1
    @96
    @67
    syl2an
    matecld
    @95
    @54
    @97
    @96
    adantl
    vl
    @11
    @8
    cP
    cR
    c.x
    cE
    @56
    @68
    cY
    @37
    @90
    @61
    mp2pm2mplem2.p
    mp2pm2mp.y
    mp2pm2mp.m
    @69
    mp2pm2mp.e
    coe1tm
    syl3anc
    vl
    cv
    #
    cK
    wceq
    #
    @100
    @38
    wceq
    @98
    @102
    @99
    @36
    @11
    @37
    @101
    cK
    @8
    eqeq1
    ifbid
    adantl
    @3
    @4
    @42
    @43
    @95
    simpl1r
    @38
    cvv
    wcel
    @98
    @36
    @11
    @37
    @6
    @7
    @10
    ovex
    cR
    c0g
    fvex
    ifex
    a1i
    fvmptd
    mpteq2dva
    oveq2d
    mpt2eq3dva
    ad2antrr
    @19
    cK
    clt
    wbr
    #
    @29
    @41
    @18
    wceq
    #
    wi
    @29
    @103
    @104
    @5
    @27
    @26
    @103
    @104
    wi
    #
    @4
    @3
    @27
    @26
    @105
    wi
    wi
    #
    @4
    @3
    @106
    wi
    @4
    @26
    @3
    @27
    @4
    @105
    @4
    @26
    @3
    @27
    @4
    @105
    wi
    wi
    wi
    #
    @4
    @26
    wa
    @103
    @18
    @23
    wceq
    #
    wi
    #
    @107
    @25
    @109
    vx
    cK
    cn0
    @20
    cK
    wceq
    #
    @21
    @103
    @24
    @108
    @20
    cK
    @19
    clt
    breq2
    @110
    @22
    @18
    @23
    @20
    cK
    @9
    fveq2
    eqeq1d
    imbi12d
    rspcva
    @4
    @3
    @27
    @109
    @105
    @4
    @3
    @27
    @109
    @105
    wi
    @4
    @3
    wa
    #
    @27
    wa
    @103
    @108
    @104
    @111
    @27
    @103
    @108
    @104
    wi
    @111
    @27
    @103
    wa
    #
    wa
    #
    @108
    @104
    @113
    @108
    wa
    #
    vi
    vj
    cN
    cN
    @37
    cmpt2
    #
    @23
    @41
    @18
    @3
    @115
    @23
    wceq
    #
    @4
    @112
    @108
    @0
    @1
    @116
    @2
    @89
    @23
    @115
    cA
    cR
    vi
    vj
    cN
    @37
    mp2pm2mp.a
    @90
    mat0op
    eqcomd
    3adant3
    ad3antlr
    @114
    vi
    vj
    cN
    cN
    @40
    @37
    @114
    @42
    @43
    w3a
    #
    @40
    cR
    vk
    @30
    @37
    cmpt
    #
    cgsu
    co
    #
    @37
    @117
    @39
    @118
    cR
    cgsu
    @117
    vk
    @30
    @38
    @37
    @117
    @95
    wa
    @36
    @11
    @37
    @117
    @95
    @36
    wn
    #
    @114
    @42
    @95
    @120
    wi
    #
    @43
    @113
    @121
    @108
    @111
    @112
    @121
    @4
    @112
    @121
    wi
    @3
    @95
    @112
    @4
    @120
    @95
    @54
    @27
    @8
    @19
    cle
    wbr
    #
    w3a
    @112
    @4
    @120
    wi
    #
    wi
    #
    @8
    @19
    elfz2nn0
    @54
    @122
    @124
    @27
    @54
    @122
    @124
    @54
    @112
    @122
    @123
    @54
    @27
    @103
    @122
    @123
    wi
    @54
    @27
    wa
    #
    @4
    @122
    @103
    @120
    @125
    @4
    @122
    @103
    @120
    @125
    @4
    wa
    #
    @122
    @103
    wa
    #
    @8
    cK
    clt
    wbr
    #
    @120
    @126
    @8
    cr
    wcel
    #
    @19
    cr
    wcel
    #
    cK
    cr
    wcel
    #
    @127
    @128
    wi
    @54
    @129
    @27
    @4
    @8
    nn0re
    #
    ad2antrr
    @27
    @130
    @54
    @4
    @19
    nn0re
    #
    ad2antlr
    @4
    @131
    @125
    cK
    nn0re
    #
    adantl
    @8
    @19
    cK
    lelttr
    syl3anc
    @126
    @128
    @120
    @126
    @128
    wa
    #
    @120
    cK
    @8
    clt
    wbr
    #
    @128
    wo
    #
    @135
    @128
    @136
    @126
    @128
    simpr
    olcd
    @120
    cK
    @8
    wne
    #
    @135
    @137
    cK
    @8
    df-ne
    @126
    @138
    @137
    wb
    #
    @128
    @4
    @131
    @129
    @139
    @125
    @134
    @54
    @129
    @27
    @132
    adantr
    cK
    @8
    lttri2
    syl2anr
    adantr
    syl5bbr
    mpbird
    ex
    syld
    exp4b
    com24
    expimpd
    com23
    imp
    3adant2
    sylbi
    com13
    adantr
    imp
    adantr
    3ad2ant1
    imp
    iffalsed
    mpteq2dva
    oveq2d
    @114
    @42
    @119
    @37
    wceq
    #
    @43
    @3
    @140
    @4
    @112
    @108
    @3
    cR
    cmnd
    wcel
    #
    @30
    cvv
    wcel
    @140
    @1
    @0
    @141
    @2
    cR
    ringmnd
    3ad2ant2
    #
    cc0
    @19
    cfz
    ovex
    @30
    vk
    cR
    cvv
    @37
    @90
    gsumz
    sylancl
    ad3antlr
    3ad2ant1
    eqtrd
    mpt2eq3dva
    @113
    @108
    simpr
    3eqtr4d
    ex
    expr
    a2d
    exp31
    com14
    syl
    ex
    com25
    pm2.43i
    impcom
    imp31
    com12
    @103
    wn
    #
    @29
    @104
    @143
    @29
    wa
    #
    @41
    vi
    vj
    cN
    cN
    vk
    cK
    @11
    csb
    #
    cmpt2
    #
    @18
    @144
    vi
    vj
    cN
    cN
    @40
    @145
    @144
    @42
    @43
    w3a
    #
    @11
    vk
    @39
    cR
    @30
    cvv
    cK
    @37
    @90
    @144
    @42
    @141
    @43
    @29
    @141
    @143
    @3
    @141
    @4
    @27
    @26
    @142
    ad3antrrr
    adantl
    3ad2ant1
    @147
    cc0
    @19
    cfz
    ovexd
    @144
    @42
    cK
    @30
    wcel
    #
    @43
    @29
    @143
    @148
    @28
    @143
    @148
    wi
    #
    @26
    @4
    @27
    @149
    @3
    @4
    @27
    wa
    #
    @143
    cK
    @19
    cle
    wbr
    #
    @148
    @4
    @131
    @130
    @151
    @143
    wb
    @27
    @134
    @133
    cK
    @19
    lenlt
    syl2an
    @150
    @151
    @148
    @150
    @151
    wa
    @4
    @27
    @151
    @148
    @4
    @27
    @151
    simpll
    @4
    @27
    @151
    simplr
    @150
    @151
    simpr
    cK
    @19
    elfz2nn0
    syl3anbrc
    ex
    sylbird
    adantll
    adantr
    impcom
    3ad2ant1
    vk
    @30
    @38
    @8
    cK
    wceq
    #
    @11
    @37
    cif
    #
    @36
    @152
    wb
    @38
    @153
    wceq
    cK
    @8
    eqcom
    @36
    @152
    @11
    @37
    ifbi
    ax-mp
    mpteq2i
    @147
    @57
    vk
    @30
    @95
    @147
    @54
    @57
    @96
    @147
    @54
    wa
    cA
    @60
    cR
    @6
    @7
    @56
    @10
    cN
    mp2pm2mp.a
    @61
    @62
    @144
    @42
    @43
    @54
    simpl2
    @144
    @42
    @43
    @54
    simpl3
    @147
    @2
    @54
    @63
    @144
    @42
    @2
    @43
    @29
    @2
    @143
    @65
    adantl
    3ad2ant1
    @67
    sylan
    matecld
    sylan2
    ralrimiva
    gsummpt1n0
    mpt2eq3dva
    @29
    @146
    @18
    wceq
    #
    @143
    @5
    @154
    @27
    @26
    @5
    @154
    va
    cv
    #
    vb
    cv
    #
    @146
    co
    @155
    @156
    @18
    co
    #
    wceq
    #
    vb
    cN
    wral
    va
    cN
    wral
    #
    @5
    @158
    va
    vb
    cN
    cN
    @5
    @155
    cN
    wcel
    #
    @156
    cN
    wcel
    #
    wa
    #
    wa
    #
    vi
    vj
    @155
    @156
    cN
    cN
    @6
    @7
    @18
    co
    #
    @157
    @146
    cvv
    @163
    vi
    vj
    cN
    cN
    @145
    @164
    @4
    @145
    @164
    wceq
    @3
    @162
    @4
    @145
    @6
    @7
    vk
    cK
    @10
    csb
    #
    co
    #
    @164
    vk
    cK
    @6
    @7
    @10
    csbov
    #
    @4
    @165
    @18
    @6
    @7
    @165
    @18
    wceq
    @4
    vk
    cK
    @9
    csbfv
    #
    a1i
    oveqd
    syl5eq
    ad2antlr
    mpt2eq3dv
    vi
    va
    weq
    vj
    vb
    weq
    wa
    @164
    @157
    wceq
    @163
    @6
    @155
    @7
    @156
    @18
    oveq12
    adantl
    @5
    @160
    @161
    simprl
    @5
    @160
    @161
    simprr
    @163
    @155
    @156
    @18
    ovexd
    ovmpt2d
    ralrimivva
    @5
    @146
    @60
    wcel
    @18
    @60
    wcel
    #
    @154
    @159
    wb
    @5
    vi
    vj
    cA
    @60
    @145
    cR
    @56
    cN
    crg
    mp2pm2mp.a
    @61
    @62
    @0
    @1
    @2
    @4
    simpl1
    @58
    @97
    @145
    @164
    @56
    @145
    @166
    @164
    @167
    @165
    @18
    @6
    @7
    @168
    oveqi
    eqtri
    @97
    cA
    @60
    cR
    @6
    @7
    @56
    @18
    cN
    mp2pm2mp.a
    @61
    @62
    @5
    @42
    @43
    simp2
    @5
    @42
    @43
    simp3
    @5
    @42
    @169
    @43
    @2
    @0
    @4
    @169
    @1
    @9
    cL
    cQ
    cA
    cO
    @60
    cK
    @66
    mp2pm2mp.l
    mp2pm2mp.q
    @62
    coe1fvalcl
    3ad2antl3
    #
    3ad2ant1
    matecld
    syl5eqel
    matbas2d
    @170
    cA
    @60
    cR
    va
    vb
    cN
    @146
    @18
    mp2pm2mp.a
    @62
    eqmat
    syl2anc
    mpbird
    ad2antrr
    adantl
    eqtrd
    ex
    pm2.61i
    3eqtrd
    @5
    @9
    @23
    cfsupp
    wbr
    #
    @26
    vs
    cn0
    wrex
    #
    @5
    @2
    @171
    @64
    @9
    cL
    cQ
    cA
    cO
    @23
    @66
    mp2pm2mp.l
    mp2pm2mp.q
    @23
    eqid
    #
    coe1sfi
    syl
    @5
    @9
    @60
    cn0
    cmap
    co
    #
    wcel
    #
    @23
    cvv
    wcel
    @171
    @172
    wi
    @5
    @2
    @9
    @20
    @23
    cfsupp
    wbr
    #
    vx
    @174
    crab
    wcel
    @175
    @64
    @9
    cL
    cQ
    cA
    vx
    cO
    @60
    @23
    @66
    mp2pm2mp.l
    mp2pm2mp.q
    @173
    @62
    coe1fsupp
    @176
    vx
    @9
    @174
    elrabi
    3syl
    cA
    c0g
    fvex
    vx
    @60
    vs
    @9
    cvv
    @23
    fsuppmapnn0ub
    sylancl
    mpd
    r19.29a
    eqtrd
end
