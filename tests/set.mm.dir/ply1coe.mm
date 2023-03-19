include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "cn0.mm"
include "cmap.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cur.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt.mm"
include "cgsu.mm"
include "c0.mm"
include "com.mm"
include "eqid.mm"
include "psr1baslem.mm"
include "1onn.mm"
include "a1i.mm"
include "cps1.mm"
include "ply1bas.mm"
include "ply1vsca.mm"
include "simpl.mm"
include "simpr.mm"
include "mplcoe1.mm"
include "fvcoe1.mm"
include "adantll.mm"
include "cmgp.mm"
include "cmvr.mm"
include "cmg.mm"
include "simpll.mm"
include "cplusg.mm"
include "csn.mm"
include "wral.mm"
include "eqidd.mm"
include "0ex.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "ralsn.mm"
include "sylibr.mm"
include "ralbidv.mm"
include "df1o2.mm"
include "raleqi.mm"
include "raleqbii.mm"
include "mplcoe5.mm"
include "mpteq1.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "cmnd.mm"
include "cvv.mm"
include "mplring.mm"
include "mpan.mm"
include "ringmgp.mm"
include "syl.mm"
include "ad2antrr.mm"
include "cbs.mm"
include "mgpbas.mm"
include "wss.mm"
include "ssv.mm"
include "ovexd.mm"
include "cmulr.mm"
include "ply1mulr.mm"
include "mgpplusg.mm"
include "eqtr3i.mm"
include "oveqi.mm"
include "mulgpropd.mm"
include "oveqd.mm"
include "adantr.mm"
include "ply1ring.mm"
include "wf.mm"
include "elmapi.mm"
include "0lt1o.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "adantl.mm"
include "vr1cl.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "vr1val.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "gsumsn.mm"
include "syl5eq.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"
include "ccom.mm"
include "nn0ex.mm"
include "mptex.mm"
include "cpl1.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ply1plusg.mm"
include "gsumpropd.mm"
include "ply1mpl0.mm"
include "clmod.mm"
include "ccmn.mm"
include "mpllmod.mm"
include "sylancr.mm"
include "lmodcmn.mm"
include "csca.mm"
include "ply1lmod.mm"
include "coe1f.mm"
include "ffvelrnda.mm"
include "ply1sca.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "lmodvscl.mm"
include "fmptd.mm"
include "ply1coefsupp.mm"
include "wf1o.mm"
include "mapsnf1o2.mm"
include "gsumf1o.mm"
include "oveq1.mm"
include "fmptco.mm"
include "3eqtrrd.mm"

theorem ply1coe
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let vk: setvar k
  let c.ex: class .^
  let cK: class K
  let cM: class M
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vd: setvar d
  assume ply1coe.p: |- P = ( Poly1 ` R )
  assume ply1coe.x: |- X = ( var1 ` R )
  assume ply1coe.b: |- B = ( Base ` P )
  assume ply1coe.n: |- .x. = ( .s ` P )
  assume ply1coe.m: |- M = ( mulGrp ` P )
  assume ply1coe.e: |- .^ = ( .g ` M )
  assume ply1coe.a: |- A = ( coe1 ` K )

  disjoint A k
  disjoint B k
  disjoint K k
  disjoint X k
  disjoint .^ k
  disjoint R k
  disjoint .x. k
  disjoint P k
  disjoint a k
  disjoint A a
  disjoint a b
  disjoint a c
  disjoint B a
  disjoint b c
  disjoint b k
  disjoint B b
  disjoint c k
  disjoint B c
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint B x
  disjoint a d
  disjoint K a
  disjoint b d
  disjoint K b
  disjoint c d
  disjoint K c
  disjoint d k
  disjoint K d
  disjoint K x
  disjoint M a
  disjoint M b
  disjoint X a
  disjoint X c
  disjoint .^ a
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint d x
  disjoint R x
  disjoint .x. a
  disjoint .x. b
  assert |- ( ( R e. Ring /\ K e. B ) -> K = ( P gsum ( k e. NN0 |-> ( ( A ` k ) .x. ( k .^ X ) ) ) ) )

  proof
    cR
    crg
    wcel
    #
    cK
    cB
    wcel
    #
    wa
    #
    cK
    c1o
    cR
    cmpl
    co
    #
    va
    cn0
    c1o
    cmap
    co
    #
    va
    cv
    #
    cK
    cfv
    #
    vb
    @4
    vb
    cv
    #
    @5
    wceq
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    cmpt
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    @3
    va
    @4
    c0
    @5
    cfv
    #
    cA
    cfv
    #
    @13
    cX
    c.ex
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cP
    vk
    cn0
    vk
    cv
    #
    cA
    cfv
    #
    @19
    cX
    c.ex
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @2
    vb
    cB
    @4
    @3
    cR
    c.x
    @8
    vd
    va
    c1o
    com
    cK
    @9
    @3
    eqid
    #
    vd
    psr1baslem
    #
    @9
    eqid
    #
    @8
    eqid
    #
    c1o
    com
    wcel
    #
    @2
    1onn
    a1i
    cP
    cR
    cR
    cps1
    cfv
    #
    cB
    ply1coe.p
    @30
    eqid
    ply1coe.b
    ply1bas
    #
    cR
    @3
    c.x
    cP
    ply1coe.p
    @25
    ply1coe.n
    ply1vsca
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    mplcoe1
    @2
    @12
    @17
    @3
    cgsu
    @2
    va
    @4
    @11
    @16
    @2
    @5
    @4
    wcel
    #
    wa
    #
    @6
    @14
    @10
    @15
    c.x
    @1
    @33
    @6
    @14
    wceq
    @0
    cA
    cK
    cB
    @5
    ply1coe.a
    fvcoe1
    adantll
    @34
    @10
    @3
    cmgp
    cfv
    #
    vc
    c1o
    vc
    cv
    #
    @5
    cfv
    #
    @36
    c1o
    cR
    cmvr
    co
    #
    cfv
    #
    @35
    cmg
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @13
    cX
    @40
    co
    #
    @15
    @34
    vx
    vb
    @4
    @3
    cR
    @8
    vd
    vc
    @40
    @35
    c1o
    @38
    com
    @5
    @9
    @25
    @26
    @27
    @28
    @29
    @34
    1onn
    a1i
    @35
    eqid
    #
    @40
    eqid
    #
    @38
    eqid
    @0
    @1
    @33
    simpll
    @2
    @33
    simpr
    @34
    @7
    @38
    cfv
    #
    vx
    cv
    #
    @38
    cfv
    #
    @35
    cplusg
    cfv
    #
    co
    #
    @49
    @47
    @50
    co
    #
    wceq
    #
    vb
    c0
    csn
    #
    wral
    #
    vx
    @54
    wral
    #
    @53
    vb
    c1o
    wral
    #
    vx
    c1o
    wral
    @34
    @47
    c0
    @38
    cfv
    #
    @50
    co
    #
    @58
    @47
    @50
    co
    #
    wceq
    #
    vb
    @54
    wral
    #
    @56
    @34
    @58
    @58
    @50
    co
    #
    @63
    wceq
    #
    @62
    @34
    @63
    eqidd
    @61
    @64
    vb
    c0
    0ex
    @7
    c0
    wceq
    #
    @59
    @63
    @60
    @63
    @65
    @47
    @58
    @58
    @50
    @7
    c0
    @38
    fveq2
    #
    oveq1d
    @65
    @47
    @58
    @58
    @50
    @66
    oveq2d
    eqeq12d
    ralsn
    sylibr
    @55
    @62
    vx
    c0
    0ex
    @48
    c0
    wceq
    #
    @53
    @61
    vb
    @54
    @67
    @51
    @59
    @52
    @60
    @67
    @49
    @58
    @47
    @50
    @48
    c0
    @38
    fveq2
    #
    oveq2d
    @67
    @49
    @58
    @47
    @50
    @68
    oveq1d
    eqeq12d
    ralbidv
    ralsn
    sylibr
    @57
    @55
    vx
    c1o
    @54
    df1o2
    @53
    vb
    c1o
    @54
    df1o2
    raleqi
    raleqbii
    sylibr
    mplcoe5
    @34
    @43
    @35
    vc
    @54
    @41
    cmpt
    #
    cgsu
    co
    #
    @44
    @42
    @69
    @35
    cgsu
    c1o
    @54
    wceq
    @42
    @69
    wceq
    df1o2
    vc
    c1o
    @54
    @41
    mpteq1
    ax-mp
    oveq2i
    @34
    @35
    cmnd
    wcel
    #
    c0
    cvv
    wcel
    #
    @44
    cB
    wcel
    @70
    @44
    wceq
    @0
    @71
    @1
    @33
    @0
    @3
    crg
    wcel
    #
    @71
    @29
    @0
    @73
    1onn
    @3
    cR
    c1o
    com
    @25
    mplring
    mpan
    @3
    @35
    @45
    ringmgp
    syl
    ad2antrr
    @72
    @34
    0ex
    a1i
    @34
    @44
    @15
    cB
    @2
    @44
    @15
    wceq
    @33
    @2
    @40
    c.ex
    @13
    cX
    @2
    va
    vb
    cB
    @40
    c.ex
    @35
    cM
    cvv
    @46
    ply1coe.e
    cB
    @35
    cbs
    cfv
    wceq
    @2
    cB
    @3
    @35
    @45
    @31
    mgpbas
    #
    a1i
    cB
    cM
    cbs
    cfv
    wceq
    @2
    cB
    cP
    cM
    ply1coe.m
    ply1coe.b
    mgpbas
    #
    a1i
    cB
    cvv
    wss
    @2
    cB
    ssv
    a1i
    @2
    @5
    cvv
    wcel
    @7
    cvv
    wcel
    wa
    wa
    #
    @5
    @7
    @50
    ovexd
    @5
    @7
    @50
    co
    @5
    @7
    cM
    cplusg
    cfv
    #
    co
    wceq
    @76
    @50
    @77
    @5
    @7
    cP
    cmulr
    cfv
    #
    @50
    @77
    @3
    @78
    @35
    @45
    cR
    @3
    @78
    cP
    ply1coe.p
    @25
    @78
    eqid
    #
    ply1mulr
    mgpplusg
    cP
    @78
    cM
    ply1coe.m
    @79
    mgpplusg
    eqtr3i
    oveqi
    a1i
    mulgpropd
    oveqd
    adantr
    #
    @34
    cM
    cmnd
    wcel
    #
    @13
    cn0
    wcel
    #
    cX
    cB
    wcel
    #
    @15
    cB
    wcel
    @0
    @81
    @1
    @33
    @0
    cP
    crg
    wcel
    @81
    cP
    cR
    ply1coe.p
    ply1ring
    cP
    cM
    ply1coe.m
    ringmgp
    syl
    #
    ad2antrr
    @33
    @82
    @2
    @33
    c1o
    cn0
    @5
    wf
    c0
    c1o
    wcel
    @82
    @5
    cn0
    c1o
    elmapi
    0lt1o
    c1o
    cn0
    c0
    @5
    ffvelrn
    sylancl
    adantl
    #
    @0
    @83
    @1
    @33
    cB
    cP
    cR
    cX
    ply1coe.x
    ply1coe.p
    ply1coe.b
    vr1cl
    #
    ad2antrr
    cB
    c.ex
    cM
    @13
    cX
    @75
    ply1coe.e
    mulgnn0cl
    syl3anc
    eqeltrd
    @41
    cB
    @44
    vc
    @35
    c0
    cvv
    @74
    @36
    c0
    wceq
    #
    @37
    @13
    @39
    cX
    @40
    @36
    c0
    @5
    fveq2
    @87
    @39
    @58
    cX
    @36
    c0
    @38
    fveq2
    cR
    cX
    ply1coe.x
    vr1val
    syl6eqr
    oveq12d
    gsumsn
    syl3anc
    syl5eq
    @80
    3eqtrd
    oveq12d
    mpteq2dva
    oveq2d
    @2
    @24
    @3
    @23
    cgsu
    co
    @3
    @23
    va
    @4
    @13
    cmpt
    #
    ccom
    #
    cgsu
    co
    @18
    @2
    @23
    cP
    @3
    cvv
    cvv
    cvv
    @23
    cvv
    wcel
    @2
    vk
    cn0
    @22
    nn0ex
    mptex
    a1i
    cP
    cvv
    wcel
    @2
    cP
    cR
    cpl1
    cfv
    cvv
    ply1coe.p
    cR
    cpl1
    fvex
    eqeltri
    a1i
    @2
    c1o
    cR
    cmpl
    ovexd
    cP
    cbs
    cfv
    #
    @3
    cbs
    cfv
    #
    wceq
    @2
    cB
    @90
    @91
    ply1coe.b
    @31
    eqtr3i
    a1i
    cP
    cplusg
    cfv
    #
    @3
    cplusg
    cfv
    wceq
    @2
    @92
    cR
    @3
    cP
    ply1coe.p
    @25
    @92
    eqid
    ply1plusg
    a1i
    gsumpropd
    @2
    cn0
    cB
    @4
    @23
    @3
    @88
    cvv
    cP
    c0g
    cfv
    #
    @31
    cP
    cR
    @3
    @93
    @25
    ply1coe.p
    @93
    eqid
    ply1mpl0
    @2
    @3
    clmod
    wcel
    #
    @3
    ccmn
    wcel
    @2
    @29
    @0
    @94
    1onn
    @32
    @3
    cR
    c1o
    com
    @25
    mpllmod
    sylancr
    @3
    lmodcmn
    syl
    cn0
    cvv
    wcel
    @2
    nn0ex
    a1i
    @2
    vk
    cn0
    @22
    cB
    @23
    @2
    @19
    cn0
    wcel
    #
    wa
    #
    cP
    clmod
    wcel
    #
    @20
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @21
    cB
    wcel
    #
    @22
    cB
    wcel
    @0
    @97
    @1
    @95
    cP
    cR
    ply1coe.p
    ply1lmod
    ad2antrr
    @96
    @20
    cR
    cbs
    cfv
    #
    @99
    @2
    cn0
    @101
    @19
    cA
    @1
    cn0
    @101
    cA
    wf
    @0
    cA
    cB
    cP
    cR
    cK
    @101
    ply1coe.a
    ply1coe.b
    ply1coe.p
    @101
    eqid
    coe1f
    adantl
    ffvelrnda
    @96
    @98
    cR
    cbs
    @0
    @98
    cR
    wceq
    @1
    @95
    @0
    cR
    @98
    cP
    cR
    crg
    ply1coe.p
    ply1sca
    eqcomd
    ad2antrr
    fveq2d
    eleqtrrd
    @96
    @81
    @95
    @83
    @100
    @0
    @81
    @1
    @95
    @84
    ad2antrr
    @2
    @95
    simpr
    @0
    @83
    @1
    @95
    @86
    ad2antrr
    cB
    c.ex
    cM
    @19
    cX
    @75
    ply1coe.e
    mulgnn0cl
    syl3anc
    @20
    c.x
    @98
    @99
    cB
    cP
    @21
    ply1coe.b
    @98
    eqid
    ply1coe.n
    @99
    eqid
    lmodvscl
    syl3anc
    @23
    eqid
    fmptd
    cA
    cB
    cP
    cR
    c.x
    vk
    c.ex
    cK
    cM
    cX
    ply1coe.p
    ply1coe.x
    ply1coe.b
    ply1coe.n
    ply1coe.m
    ply1coe.e
    ply1coe.a
    ply1coefsupp
    @4
    cn0
    @88
    wf1o
    @2
    va
    cn0
    c1o
    @88
    c0
    df1o2
    nn0ex
    0ex
    @88
    eqid
    mapsnf1o2
    a1i
    gsumf1o
    @2
    @89
    @17
    @3
    cgsu
    @2
    va
    vk
    @4
    cn0
    @13
    @22
    @16
    @88
    @23
    @85
    @2
    @88
    eqidd
    @2
    @23
    eqidd
    @19
    @13
    wceq
    @20
    @14
    @21
    @15
    c.x
    @19
    @13
    cA
    fveq2
    @19
    @13
    cX
    c.ex
    oveq1
    oveq12d
    fmptco
    oveq2d
    3eqtrrd
    3eqtrd
end
