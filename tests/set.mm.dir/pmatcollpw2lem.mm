include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cn0.mm"
include "cv.mm"
include "cdecpmat.mm"
include "co.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "c0g.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "wne.mm"
include "crab.mm"
include "wfn.mm"
include "cvv.mm"
include "wceq.mm"
include "wral.mm"
include "simp1.mm"
include "mpt2exga.mm"
include "syl2anc.mm"
include "ralrimivw.mm"
include "eqid.mm"
include "fnmpt.mm"
include "syl.mm"
include "nn0ex.mm"
include "a1i.mm"
include "fvexd.mm"
include "suppvalfn.mm"
include "syl3anc.mm"
include "clt.mm"
include "wn.mm"
include "wi.mm"
include "wrex.mm"
include "wa.mm"
include "cco1.mm"
include "pmatcoe1fsupp.mm"
include "oveq1.mm"
include "csca.mm"
include "cvsca.mm"
include "ply1sca.mm"
include "3ad2ant2.mm"
include "fveq2d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "ad3antrrr.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "cbs.mm"
include "simpl2.mm"
include "cmgp.mm"
include "ply1moncl.mm"
include "3ad2antl2.mm"
include "jca.mm"
include "adantr.mm"
include "ply10s0.mm"
include "3eqtrd.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "anasss.mm"
include "ralimdvva.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "reximdv.mm"
include "mpd.mm"
include "simpl3.mm"
include "simpr.mm"
include "3jca.mm"
include "decpmate.mm"
include "sylan.mm"
include "eqeq1d.mm"
include "2ralbidva.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "wb.mm"
include "biantrur.mm"
include "bicomi.mm"
include "ralbii.mm"
include "bitr3i.mm"
include "rexralbidv.mm"
include "mpt2eq123.mm"
include "imim2i.mm"
include "ralimi.mm"
include "reximi.mm"
include "oveq2.mm"
include "oveqd.mm"
include "oveq12d.mm"
include "mpt2eq3dv.mm"
include "adantl.mm"
include "id.mm"
include "ancri.mm"
include "3ad2ant1.mm"
include "fvmptd.mm"
include "ply1ring.mm"
include "anim2i.mm"
include "3adant3.mm"
include "mat0op.mm"
include "eqeq12d.mm"
include "nne.mm"
include "imbi2i.mm"
include "rexbii.mm"
include "sylibr.mm"
include "rabssnn0fi.mm"
include "eqeltrd.mm"
include "wfun.mm"
include "funmpt.mm"
include "mptex.mm"
include "funisfsupp.mm"

theorem pmatcollpw2lem
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let c.xp: class .X.
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let c.ex: class .^
  let cM: class M
  let cN: class N
  let cX: class X
  let vs: setvar s
  let vx: setvar x
  let cI: class I
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  assume pmatcollpw1.p: |- P = ( Poly1 ` R )
  assume pmatcollpw1.c: |- C = ( N Mat P )
  assume pmatcollpw1.b: |- B = ( Base ` C )
  assume pmatcollpw1.m: |- .X. = ( .s ` P )
  assume pmatcollpw1.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume pmatcollpw1.x: |- X = ( var1 ` R )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint X n
  disjoint .X. n
  disjoint .^ n
  disjoint P n
  disjoint B i
  disjoint B j
  disjoint i j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint P i
  disjoint P j
  disjoint i n
  disjoint j n
  disjoint R i
  disjoint R j
  disjoint X i
  disjoint X j
  disjoint .X. i
  disjoint .X. j
  disjoint .^ i
  disjoint .^ j
  disjoint B s
  disjoint B x
  disjoint n s
  disjoint n x
  disjoint s x
  disjoint I n
  disjoint I s
  disjoint I x
  disjoint J n
  disjoint J s
  disjoint J x
  disjoint M s
  disjoint M x
  disjoint N s
  disjoint N x
  disjoint P s
  disjoint P x
  disjoint R s
  disjoint R x
  disjoint X s
  disjoint X x
  disjoint .X. s
  disjoint .X. x
  disjoint .^ s
  disjoint .^ x
  disjoint a n
  disjoint b n
  disjoint B a
  disjoint B b
  disjoint a b
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint M a
  disjoint M b
  disjoint N a
  disjoint N b
  disjoint P a
  disjoint P b
  disjoint R a
  disjoint R b
  disjoint X a
  disjoint X b
  disjoint .X. a
  disjoint .X. b
  disjoint .^ a
  disjoint .^ b
  disjoint B y
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint n y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint M y
  disjoint N y
  disjoint R y
  disjoint X y
  disjoint .X. y
  disjoint .^ y
  assert |- ( ( N e. Fin /\ R e. Ring /\ M e. B ) -> ( n e. NN0 |-> ( i e. N , j e. N |-> ( ( i ( M decompPMat n ) j ) .X. ( n .^ X ) ) ) ) finSupp ( 0g ` C ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    vn
    cn0
    vi
    vj
    cN
    cN
    vi
    cv
    #
    vj
    cv
    #
    cM
    vn
    cv
    #
    cdecpmat
    co
    #
    co
    #
    @6
    cX
    c.ex
    co
    #
    c.xp
    co
    #
    cmpt2
    #
    cmpt
    #
    cC
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @12
    @13
    csupp
    co
    #
    cfn
    wcel
    #
    @3
    @15
    vx
    cv
    #
    @12
    cfv
    #
    @13
    wne
    #
    vx
    cn0
    crab
    #
    cfn
    @3
    @12
    cn0
    wfn
    #
    cn0
    cvv
    wcel
    #
    @13
    cvv
    wcel
    #
    @15
    @20
    wceq
    @3
    @11
    cvv
    wcel
    #
    vn
    cn0
    wral
    @21
    @3
    @24
    vn
    cn0
    @3
    @0
    @0
    @24
    @0
    @1
    @2
    simp1
    #
    @25
    vi
    vj
    cN
    cN
    @10
    cfn
    cfn
    mpt2exga
    syl2anc
    ralrimivw
    vn
    cn0
    @11
    @12
    cvv
    @12
    eqid
    fnmpt
    syl
    @22
    @3
    nn0ex
    a1i
    @3
    cC
    c0g
    fvexd
    #
    vx
    @12
    cvv
    cvv
    cn0
    @13
    suppvalfn
    syl3anc
    @3
    vy
    cv
    @17
    clt
    wbr
    #
    @19
    wn
    #
    wi
    #
    vx
    cn0
    wral
    #
    vy
    cn0
    wrex
    #
    @20
    cfn
    wcel
    @3
    @27
    @18
    @13
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vy
    cn0
    wrex
    #
    @31
    @3
    @35
    @27
    vi
    vj
    cN
    cN
    @4
    @5
    cM
    @17
    cdecpmat
    co
    #
    co
    #
    @17
    cX
    c.ex
    co
    #
    c.xp
    co
    #
    cmpt2
    #
    vi
    vj
    cN
    cN
    cP
    c0g
    cfv
    #
    cmpt2
    #
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vy
    cn0
    wrex
    #
    @3
    @27
    cN
    cN
    wceq
    #
    @47
    @39
    @41
    wceq
    #
    vj
    cN
    wral
    #
    wa
    #
    vi
    cN
    wral
    #
    wa
    #
    wi
    #
    vx
    cn0
    wral
    #
    vy
    cn0
    wrex
    #
    @46
    @3
    @55
    @27
    @49
    vi
    cN
    wral
    #
    wi
    #
    vx
    cn0
    wral
    #
    vy
    cn0
    wrex
    #
    @3
    @59
    @27
    @17
    @4
    @5
    cM
    co
    cco1
    cfv
    cfv
    #
    @38
    c.xp
    co
    #
    @41
    wceq
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    wi
    #
    vx
    cn0
    wral
    #
    vy
    cn0
    wrex
    #
    @3
    @27
    @60
    cR
    c0g
    cfv
    #
    wceq
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    wi
    #
    vx
    cn0
    wral
    #
    vy
    cn0
    wrex
    @66
    vx
    cB
    cC
    cP
    cR
    vi
    vj
    cM
    cN
    @67
    vy
    pmatcollpw1.p
    pmatcollpw1.c
    pmatcollpw1.b
    @67
    eqid
    #
    pmatcoe1fsupp
    @3
    @71
    @65
    vy
    cn0
    @3
    @70
    @64
    vx
    cn0
    @3
    @17
    cn0
    wcel
    #
    wa
    #
    @69
    @63
    @27
    @74
    @68
    @62
    vi
    vj
    cN
    cN
    @74
    @4
    cN
    wcel
    #
    @5
    cN
    wcel
    #
    @68
    @62
    wi
    @74
    @75
    wa
    #
    @76
    wa
    #
    @68
    @62
    @68
    @78
    @61
    @67
    @38
    c.xp
    co
    #
    @41
    @60
    @67
    @38
    c.xp
    oveq1
    @78
    @79
    cP
    csca
    cfv
    #
    c0g
    cfv
    #
    @38
    cP
    cvsca
    cfv
    #
    co
    #
    @67
    @38
    @82
    co
    #
    @41
    @3
    @79
    @83
    wceq
    @73
    @75
    @76
    @3
    @67
    @81
    @38
    @38
    c.xp
    @82
    c.xp
    @82
    wceq
    @3
    pmatcollpw1.m
    a1i
    @3
    cR
    @80
    c0g
    @1
    @0
    cR
    @80
    wceq
    @2
    cP
    cR
    crg
    pmatcollpw1.p
    ply1sca
    3ad2ant2
    #
    fveq2d
    @3
    @38
    eqidd
    oveq123d
    ad3antrrr
    @78
    @81
    @67
    @38
    @82
    @78
    @80
    cR
    c0g
    @3
    @80
    cR
    wceq
    @73
    @75
    @76
    @3
    cR
    @80
    @85
    eqcomd
    ad3antrrr
    fveq2d
    oveq1d
    @78
    @1
    @38
    cP
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    @84
    @41
    wceq
    @77
    @88
    @76
    @74
    @88
    @75
    @74
    @1
    @87
    @0
    @1
    @2
    @73
    simpl2
    #
    @1
    @0
    @73
    @87
    @2
    @86
    @17
    cP
    cR
    c.ex
    cP
    cmgp
    cfv
    #
    cX
    pmatcollpw1.p
    pmatcollpw1.x
    @90
    eqid
    pmatcollpw1.e
    @86
    eqid
    #
    ply1moncl
    3ad2antl2
    jca
    adantr
    adantr
    @86
    cP
    cR
    @82
    @38
    @67
    pmatcollpw1.p
    @91
    @82
    eqid
    @72
    ply10s0
    syl
    3eqtrd
    sylan9eqr
    ex
    anasss
    ralimdvva
    imim2d
    ralimdva
    reximdv
    mpd
    @3
    @58
    @65
    vy
    cn0
    @3
    @57
    @64
    vx
    cn0
    @74
    @56
    @63
    @27
    @74
    @48
    @62
    vi
    vj
    cN
    cN
    @74
    @75
    @76
    wa
    #
    wa
    #
    @39
    @61
    @41
    @93
    @37
    @60
    @38
    c.xp
    @74
    @1
    @2
    @73
    w3a
    @92
    @37
    @60
    wceq
    @74
    @1
    @2
    @73
    @89
    @0
    @1
    @2
    @73
    simpl3
    @3
    @73
    simpr
    #
    3jca
    cB
    cC
    cP
    cR
    @4
    @5
    @17
    cM
    cN
    crg
    pmatcollpw1.p
    pmatcollpw1.c
    pmatcollpw1.b
    decpmate
    sylan
    oveq1d
    eqeq1d
    2ralbidva
    imbi2d
    ralbidva
    rexbidv
    mpbird
    @3
    @53
    @57
    vy
    vx
    cn0
    cn0
    @3
    @52
    @56
    @27
    @52
    @56
    wb
    @3
    @52
    @51
    @56
    @47
    @51
    cN
    eqid
    #
    biantrur
    @50
    @49
    vi
    cN
    @49
    @50
    @47
    @49
    @95
    biantrur
    bicomi
    ralbii
    bitr3i
    a1i
    imbi2d
    rexralbidv
    mpbird
    @54
    @45
    vy
    cn0
    @53
    @44
    vx
    cn0
    @52
    @43
    @27
    vi
    vj
    cN
    cN
    @39
    cN
    cN
    @41
    mpt2eq123
    imim2i
    ralimi
    reximi
    syl
    @3
    @34
    @45
    vy
    cn0
    @3
    @33
    @44
    vx
    cn0
    @74
    @32
    @43
    @27
    @74
    @18
    @40
    @13
    @42
    @74
    vn
    @17
    @11
    @40
    cn0
    @12
    cvv
    @74
    @12
    eqidd
    @6
    @17
    wceq
    #
    @11
    @40
    wceq
    @74
    @96
    vi
    vj
    cN
    cN
    @10
    @39
    @96
    @8
    @37
    @9
    @38
    c.xp
    @96
    @7
    @36
    @4
    @5
    @6
    @17
    cM
    cdecpmat
    oveq2
    oveqd
    @6
    @17
    cX
    c.ex
    oveq1
    oveq12d
    mpt2eq3dv
    adantl
    @94
    @74
    @0
    @0
    wa
    #
    @40
    cvv
    wcel
    @3
    @97
    @73
    @0
    @1
    @97
    @2
    @0
    @0
    @0
    id
    ancri
    3ad2ant1
    adantr
    vi
    vj
    cN
    cN
    @39
    cfn
    cfn
    mpt2exga
    syl
    fvmptd
    @74
    @0
    cP
    crg
    wcel
    #
    wa
    #
    @13
    @42
    wceq
    @3
    @99
    @73
    @0
    @1
    @99
    @2
    @1
    @98
    @0
    cP
    cR
    pmatcollpw1.p
    ply1ring
    anim2i
    3adant3
    adantr
    cC
    cP
    vi
    vj
    cN
    @41
    pmatcollpw1.c
    @41
    eqid
    mat0op
    syl
    eqeq12d
    imbi2d
    ralbidva
    rexbidv
    mpbird
    @30
    @34
    vy
    cn0
    @29
    @33
    vx
    cn0
    @28
    @32
    @27
    @18
    @13
    nne
    imbi2i
    ralbii
    rexbii
    sylibr
    @19
    vx
    vy
    rabssnn0fi
    sylibr
    eqeltrd
    @3
    @12
    wfun
    #
    @12
    cvv
    wcel
    #
    @23
    @14
    @16
    wb
    @100
    @3
    vn
    cn0
    @11
    funmpt
    a1i
    @101
    @3
    vn
    cn0
    @11
    nn0ex
    mptex
    a1i
    @26
    @12
    cvv
    cvv
    @13
    funisfsupp
    syl3anc
    mpbird
end
