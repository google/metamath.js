include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "cn.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wa.mm"
include "cpl1.mm"
include "cfv.mm"
include "cn0.mm"
include "cv1.mm"
include "cmgp.mm"
include "cmg.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cco1.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "eqid.mm"
include "crg.mm"
include "crngring.mm"
include "matring.mm"
include "sylan2.mm"
include "3adant3.mm"
include "adantr.mm"
include "ccom.mm"
include "cur.mm"
include "ccpmat.mm"
include "cmadu.mm"
include "cpmadumatpolylem1.mm"
include "anasss.mm"
include "wf.mm"
include "chfacfisfcpmat.mm"
include "syl3anl2.mm"
include "fvco3.mm"
include "eqcomd.mm"
include "sylan.mm"
include "elmapi.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "mpdan.mm"
include "cfsupp.mm"
include "anim2i.mm"
include "cpm2mf.mm"
include "syl.mm"
include "fcompt.mm"
include "syl2anc.mm"
include "wbr.mm"
include "cpmadumatpolylem2.mm"
include "eqbrtrrd.mm"
include "cbs.mm"
include "simpll1.mm"
include "3ad2ant2.mm"
include "ad2antrr.mm"
include "chpmatply1.mm"
include "syl5eqel.mm"
include "coe1fvalcl.mm"
include "adantlr.mm"
include "ringidcl.mm"
include "matvscl.mm"
include "syl22anc.mm"
include "cvv.mm"
include "csca.mm"
include "nn0ex.mm"
include "a1i.mm"
include "clmod.mm"
include "matlmod.mm"
include "eqidd.mm"
include "fvexd.mm"
include "matsca2.mm"
include "eqeltrrd.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "eleqtrrd.mm"
include "mptcoe1fsupp.mm"
include "mptscmfsupp0.mm"
include "fveq2.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "oveq2i.mm"
include "oveq1d.mm"
include "gsumply1eq.mm"
include "biimpa.mm"
include "eqeq12d.mm"
include "cbvralv.mm"
include "sylibr.mm"
include "ex.mm"

theorem chcoeffeqlem
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let c.xp: class .X.
  let cU: class U
  let c.1: class .1.
  let vn: setvar n
  let cG: class G
  let c.as: class .*
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let vs: setvar s
  let vb: setvar b
  let vl: setvar l
  assume chcoeffeq.a: |- A = ( N Mat R )
  assume chcoeffeq.b: |- B = ( Base ` A )
  assume chcoeffeq.p: |- P = ( Poly1 ` R )
  assume chcoeffeq.y: |- Y = ( N Mat P )
  assume chcoeffeq.r: |- .X. = ( .r ` Y )
  assume chcoeffeq.s: |- .- = ( -g ` Y )
  assume chcoeffeq.0: |- .0. = ( 0g ` Y )
  assume chcoeffeq.t: |- T = ( N matToPolyMat R )
  assume chcoeffeq.c: |- C = ( N CharPlyMat R )
  assume chcoeffeq.k: |- K = ( C ` M )
  assume chcoeffeq.g: |- G = ( n e. NN0 |-> if ( n = 0 , ( .0. .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , .0. , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )
  assume chcoeffeq.w: |- W = ( Base ` Y )
  assume chcoeffeq.1: |- .1. = ( 1r ` A )
  assume chcoeffeq.m: |- .* = ( .s ` A )
  assume chcoeffeq.u: |- U = ( N cPolyMatToMat R )

  disjoint A n
  disjoint B n
  disjoint G n
  disjoint K n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint U n
  disjoint Y n
  disjoint .1. n
  disjoint .* n
  disjoint b n
  disjoint n s
  disjoint A l
  disjoint l n
  disjoint B l
  disjoint G l
  disjoint K l
  disjoint M l
  disjoint N l
  disjoint R l
  disjoint U l
  disjoint .1. l
  disjoint .* l
  disjoint b l
  disjoint l s
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( s e. NN /\ b e. ( B ^m ( 0 ... s ) ) ) ) -> ( ( ( Poly1 ` A ) gsum ( n e. NN0 |-> ( ( U ` ( G ` n ) ) ( .s ` ( Poly1 ` A ) ) ( n ( .g ` ( mulGrp ` ( Poly1 ` A ) ) ) ( var1 ` A ) ) ) ) ) = ( ( Poly1 ` A ) gsum ( n e. NN0 |-> ( ( ( ( coe1 ` K ) ` n ) .* .1. ) ( .s ` ( Poly1 ` A ) ) ( n ( .g ` ( mulGrp ` ( Poly1 ` A ) ) ) ( var1 ` A ) ) ) ) ) -> A. n e. NN0 ( U ` ( G ` n ) ) = ( ( ( coe1 ` K ) ` n ) .* .1. ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    vs
    cv
    #
    cn
    wcel
    #
    vb
    cv
    cB
    cc0
    @4
    cfz
    co
    cmap
    co
    wcel
    #
    wa
    #
    wa
    #
    cA
    cpl1
    cfv
    #
    vn
    cn0
    vn
    cv
    #
    cG
    cfv
    #
    cU
    cfv
    #
    @10
    cA
    cv1
    cfv
    #
    @9
    cmgp
    cfv
    cmg
    cfv
    #
    co
    #
    @9
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @9
    vn
    cn0
    @10
    cK
    cco1
    cfv
    #
    cfv
    #
    c.1
    c.as
    co
    #
    @15
    @16
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    @12
    @22
    wceq
    #
    vn
    cn0
    wral
    #
    @8
    @26
    wa
    vl
    cv
    #
    cG
    cfv
    #
    cU
    cfv
    #
    @29
    @20
    cfv
    #
    c.1
    c.as
    co
    #
    wceq
    #
    vl
    cn0
    wral
    #
    @28
    @8
    @26
    @35
    @8
    @31
    @33
    @9
    @25
    cA
    vl
    @14
    @16
    cB
    @19
    @13
    cA
    c0g
    cfv
    #
    @9
    eqid
    #
    @13
    eqid
    #
    @14
    eqid
    #
    @3
    cA
    crg
    wcel
    #
    @7
    @0
    @1
    @40
    @2
    @1
    @0
    cR
    crg
    wcel
    #
    @40
    cR
    crngring
    #
    cA
    cR
    cN
    chcoeffeq.a
    matring
    sylan2
    3adant3
    #
    adantr
    chcoeffeq.b
    @16
    eqid
    #
    @36
    eqid
    #
    @8
    cU
    cG
    ccom
    #
    cB
    cn0
    cmap
    co
    wcel
    #
    @31
    cB
    wcel
    #
    vl
    cn0
    wral
    @3
    @5
    @6
    @47
    cA
    cB
    cR
    cv1
    cfv
    #
    cY
    cur
    cfv
    #
    cY
    cvsca
    cfv
    #
    co
    cM
    cT
    cfv
    c.mi
    co
    #
    cP
    @9
    cR
    cN
    cR
    ccpmat
    co
    #
    cT
    @51
    c.xp
    cU
    @50
    vn
    @14
    cG
    @16
    cN
    cP
    cmadu
    co
    #
    cM
    c.mi
    cN
    cW
    @13
    cY
    c.0
    @49
    vs
    vb
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.p
    chcoeffeq.y
    chcoeffeq.t
    chcoeffeq.r
    chcoeffeq.s
    chcoeffeq.0
    chcoeffeq.g
    @53
    eqid
    #
    @51
    eqid
    #
    @50
    eqid
    #
    @49
    eqid
    #
    @52
    eqid
    #
    @54
    eqid
    #
    chcoeffeq.w
    @37
    @38
    @44
    @39
    chcoeffeq.u
    cpmadumatpolylem1
    anasss
    @8
    @47
    wa
    #
    @48
    vl
    cn0
    @61
    @29
    cn0
    wcel
    #
    wa
    @31
    @29
    @46
    cfv
    #
    cB
    @61
    cn0
    @53
    cG
    wf
    #
    @62
    @31
    @63
    wceq
    @8
    @64
    @47
    @1
    @0
    @41
    @2
    @7
    @64
    @42
    cA
    cB
    cP
    cR
    @53
    cT
    c.xp
    vn
    cG
    cM
    c.mi
    cN
    cY
    c.0
    vs
    vb
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.p
    chcoeffeq.y
    chcoeffeq.r
    chcoeffeq.s
    chcoeffeq.0
    chcoeffeq.t
    chcoeffeq.g
    @55
    chfacfisfcpmat
    syl3anl2
    #
    adantr
    @64
    @62
    wa
    @63
    @31
    cn0
    @53
    @29
    cU
    cG
    fvco3
    eqcomd
    sylan
    @61
    cn0
    cB
    @29
    @46
    @47
    cn0
    cB
    @46
    wf
    @8
    @46
    cB
    cn0
    elmapi
    adantl
    ffvelrnda
    eqeltrd
    ralrimiva
    mpdan
    @8
    @46
    vl
    cn0
    @31
    cmpt
    #
    @36
    cfsupp
    @8
    @53
    cB
    cU
    wf
    #
    @64
    @46
    @66
    wceq
    @8
    @0
    @41
    wa
    #
    @67
    @3
    @68
    @7
    @0
    @1
    @68
    @2
    @1
    @41
    @0
    @42
    anim2i
    3adant3
    adantr
    cA
    cR
    @53
    cU
    cB
    cN
    chcoeffeq.a
    chcoeffeq.b
    @55
    chcoeffeq.u
    cpm2mf
    syl
    @65
    vl
    cU
    cG
    cn0
    @53
    cB
    fcompt
    syl2anc
    @3
    @5
    @6
    @46
    @36
    cfsupp
    wbr
    cA
    cB
    @52
    cP
    @9
    cR
    @53
    cT
    @51
    c.xp
    cU
    @50
    vn
    @14
    cG
    @16
    @54
    cM
    c.mi
    cN
    cW
    @13
    cY
    c.0
    @49
    vs
    vb
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.p
    chcoeffeq.y
    chcoeffeq.t
    chcoeffeq.r
    chcoeffeq.s
    chcoeffeq.0
    chcoeffeq.g
    @55
    @56
    @57
    @58
    @59
    @60
    chcoeffeq.w
    @37
    @38
    @44
    @39
    chcoeffeq.u
    cpmadumatpolylem2
    anasss
    eqbrtrrd
    @8
    @33
    cB
    wcel
    #
    vl
    cn0
    @8
    @62
    wa
    #
    @0
    @41
    @32
    cR
    cbs
    cfv
    #
    wcel
    #
    c.1
    cB
    wcel
    #
    @69
    @0
    @1
    @2
    @7
    @62
    simpll1
    @3
    @41
    @7
    @62
    @1
    @0
    @41
    @2
    @42
    3ad2ant2
    #
    ad2antrr
    @3
    @62
    @72
    @7
    @3
    cK
    cP
    cbs
    cfv
    #
    wcel
    @62
    @72
    @3
    cK
    cM
    cC
    cfv
    @75
    chcoeffeq.k
    cA
    cB
    cC
    cP
    cR
    @75
    cM
    cN
    chcoeffeq.c
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.p
    @75
    eqid
    #
    chpmatply1
    syl5eqel
    #
    @20
    @75
    cP
    cR
    cK
    @71
    @29
    @20
    eqid
    @76
    chcoeffeq.p
    @71
    eqid
    #
    coe1fvalcl
    sylan
    adantlr
    @3
    @73
    @7
    @62
    @3
    @40
    @73
    @43
    cB
    cA
    c.1
    chcoeffeq.b
    chcoeffeq.1
    ringidcl
    syl
    ad2antrr
    #
    cA
    cB
    @32
    cR
    c.as
    @71
    cN
    c.1
    @78
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.m
    matvscl
    syl22anc
    ralrimiva
    @8
    cvv
    cn0
    cA
    cA
    csca
    cfv
    #
    @32
    vl
    c.as
    cB
    cvv
    c.1
    @36
    @80
    c0g
    cfv
    #
    cn0
    cvv
    wcel
    @8
    nn0ex
    a1i
    @3
    cA
    clmod
    wcel
    #
    @7
    @0
    @1
    @82
    @2
    @1
    @0
    @41
    @82
    @42
    cA
    cR
    cN
    chcoeffeq.a
    matlmod
    sylan2
    3adant3
    adantr
    @8
    @80
    eqidd
    chcoeffeq.b
    @70
    @29
    @20
    fvexd
    @79
    @45
    @81
    eqid
    #
    chcoeffeq.m
    @3
    vl
    cn0
    @32
    cmpt
    @81
    cfsupp
    wbr
    #
    @7
    @3
    @80
    crg
    wcel
    cK
    @80
    cpl1
    cfv
    #
    cbs
    cfv
    #
    wcel
    @84
    @3
    cR
    @80
    crg
    @0
    @1
    cR
    @80
    wceq
    @2
    cA
    cR
    cN
    ccrg
    chcoeffeq.a
    matsca2
    3adant3
    #
    @74
    eqeltrrd
    @3
    cK
    @75
    @86
    @77
    @3
    @85
    cP
    cbs
    @3
    @85
    cR
    cpl1
    cfv
    cP
    @3
    @80
    cR
    cpl1
    @3
    cR
    @80
    @87
    eqcomd
    fveq2d
    chcoeffeq.p
    syl6eqr
    fveq2d
    eleqtrrd
    @86
    @85
    @80
    vl
    cK
    @81
    @85
    eqid
    @86
    eqid
    @83
    mptcoe1fsupp
    syl2anc
    adantr
    mptscmfsupp0
    @19
    @9
    vl
    cn0
    @31
    @29
    @13
    @14
    co
    #
    @16
    co
    #
    cmpt
    #
    cgsu
    co
    wceq
    @8
    @18
    @90
    @9
    cgsu
    vn
    vl
    cn0
    @17
    @89
    @10
    @29
    wceq
    #
    @12
    @31
    @15
    @88
    @16
    @91
    @11
    @30
    cU
    @10
    @29
    cG
    fveq2
    fveq2d
    #
    @10
    @29
    @13
    @14
    oveq1
    #
    oveq12d
    cbvmptv
    oveq2i
    a1i
    @25
    @9
    vl
    cn0
    @33
    @88
    @16
    co
    #
    cmpt
    #
    cgsu
    co
    wceq
    @8
    @24
    @95
    @9
    cgsu
    vn
    vl
    cn0
    @23
    @94
    @91
    @22
    @33
    @15
    @88
    @16
    @91
    @21
    @32
    c.1
    c.as
    @10
    @29
    @20
    fveq2
    oveq1d
    #
    @93
    oveq12d
    cbvmptv
    oveq2i
    a1i
    gsumply1eq
    biimpa
    @27
    @34
    vn
    vl
    cn0
    @91
    @12
    @31
    @22
    @33
    @92
    @96
    eqeq12d
    cbvralv
    sylibr
    ex
end
