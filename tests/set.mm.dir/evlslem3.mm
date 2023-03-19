include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "cfv.mm"
include "cof.mm"
include "co.mm"
include "cgsu.mm"
include "wcel.mm"
include "cvv.mm"
include "ccrg.mm"
include "crg.mm"
include "crngring.mm"
include "syl.mm"
include "mplmon2cl.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "wa.mm"
include "simpr.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ifexg.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "eqid.mm"
include "fvmptg.mm"
include "mpteq2dva.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "rabex2.mm"
include "crh.mm"
include "wf.mm"
include "rhmf.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "ffvelrnd.mm"
include "mgpbas.mm"
include "ccmn.mm"
include "crngmgp.mm"
include "cmnmnd.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "simprr.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "psrbagf.mm"
include "sylan.mm"
include "inidm.mm"
include "off.mm"
include "wfun.mm"
include "csupp.mm"
include "wss.mm"
include "cfsupp.mm"
include "wbr.mm"
include "ffund.mm"
include "wb.mm"
include "psrbag.mm"
include "simplbda.mm"
include "cdif.mm"
include "cc0.mm"
include "wfn.mm"
include "ffnd.mm"
include "eldifi.mm"
include "adantl.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "wn.mm"
include "wo.mm"
include "eldifn.mm"
include "ad2antlr.mm"
include "elpreima.mm"
include "mpbir2and.mm"
include "mtand.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "elnn0.mm"
include "sylib.mm"
include "orel1.mm"
include "sylc.mm"
include "mulg0.mm"
include "3eqtrd.mm"
include "suppss.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"
include "gsumcl.mm"
include "ringcl.mm"
include "fmptd.mm"
include "csn.mm"
include "eldifsni.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "cghm.mm"
include "rhmghm.mm"
include "ghmid.mm"
include "eqtrd.mm"
include "sylan2.mm"
include "ringlz.mm"
include "suppss2.mm"
include "gsumpt.mm"
include "iftrue.mm"
include "oveq1.mm"
include "oveq12d.mm"

theorem evlslem3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let vh: setvar h
  let cE: class E
  let c.ex: class .^
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let c.0: class .0.
  let vp: setvar p
  let vb: setvar b
  let vy: setvar y
  let vz: setvar z
  assume evlslem1.p: |- P = ( I mPoly R )
  assume evlslem1.b: |- B = ( Base ` P )
  assume evlslem1.c: |- C = ( Base ` S )
  assume evlslem1.k: |- K = ( Base ` R )
  assume evlslem1.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume evlslem1.t: |- T = ( mulGrp ` S )
  assume evlslem1.x: |- .^ = ( .g ` T )
  assume evlslem1.m: |- .x. = ( .r ` S )
  assume evlslem1.v: |- V = ( I mVar R )
  assume evlslem1.e: |- E = ( p e. B |-> ( S gsum ( b e. D |-> ( ( F ` ( p ` b ) ) .x. ( T gsum ( b oF .^ G ) ) ) ) ) )
  assume evlslem1.i: |- ( ph -> I e. _V )
  assume evlslem1.r: |- ( ph -> R e. CRing )
  assume evlslem1.s: |- ( ph -> S e. CRing )
  assume evlslem1.f: |- ( ph -> F e. ( R RingHom S ) )
  assume evlslem1.g: |- ( ph -> G : I --> C )
  assume evlslem3.z: |- .0. = ( 0g ` R )
  assume evlslem3.k: |- ( ph -> A e. D )
  assume evlslem3.q: |- ( ph -> H e. K )

  disjoint b p
  disjoint b x
  disjoint .0. b
  disjoint p x
  disjoint .0. p
  disjoint .0. x
  disjoint B p
  disjoint C b
  disjoint D b
  disjoint D p
  disjoint D x
  disjoint F b
  disjoint F p
  disjoint .^ b
  disjoint .^ p
  disjoint b h
  disjoint A b
  disjoint h p
  disjoint h x
  disjoint A h
  disjoint A p
  disjoint A x
  disjoint I h
  disjoint K x
  disjoint b ph
  disjoint ph x
  disjoint G b
  disjoint G p
  disjoint H b
  disjoint H p
  disjoint H x
  disjoint S b
  disjoint S p
  disjoint T b
  disjoint T p
  disjoint .x. b
  disjoint .x. p
  disjoint R x
  disjoint b y
  disjoint b z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint p y
  disjoint p z
  disjoint x y
  disjoint x z
  disjoint D y
  disjoint D z
  disjoint .^ y
  disjoint .^ z
  disjoint ph y
  disjoint ph z
  disjoint G y
  disjoint G z
  disjoint T y
  assert |- ( ph -> ( E ` ( x e. D |-> if ( x = A , H , .0. ) ) ) = ( ( F ` H ) .x. ( T gsum ( A oF .^ G ) ) ) )

  proof
    wph
    vx
    cD
    vx
    cv
    #
    cA
    wceq
    #
    cH
    c.0
    cif
    #
    cmpt
    #
    cE
    cfv
    #
    cS
    vb
    cD
    vb
    cv
    #
    @3
    cfv
    #
    cF
    cfv
    #
    cT
    @5
    cG
    c.ex
    cof
    #
    co
    #
    cgsu
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
    cA
    vb
    cD
    @5
    cA
    wceq
    #
    cH
    c.0
    cif
    #
    cF
    cfv
    #
    @10
    c.x
    co
    #
    cmpt
    #
    cfv
    #
    cH
    cF
    cfv
    #
    cT
    cA
    cG
    @8
    co
    #
    cgsu
    co
    #
    c.x
    co
    #
    wph
    @3
    cB
    wcel
    @4
    @13
    wceq
    wph
    vx
    cB
    cK
    cD
    cP
    cR
    vh
    cI
    cA
    cvv
    cH
    c.0
    evlslem1.p
    evlslem1.d
    evlslem3.z
    evlslem1.k
    evlslem1.i
    wph
    cR
    ccrg
    wcel
    cR
    crg
    wcel
    #
    evlslem1.r
    cR
    crngring
    syl
    #
    evlslem1.b
    evlslem3.q
    evlslem3.k
    mplmon2cl
    vp
    @3
    cS
    vb
    cD
    @5
    vp
    cv
    #
    cfv
    #
    cF
    cfv
    #
    @10
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    @13
    cB
    cE
    @26
    @3
    wceq
    #
    @30
    @12
    cS
    cgsu
    @31
    vb
    cD
    @29
    @11
    @31
    @28
    @7
    @10
    c.x
    @31
    @27
    @6
    cF
    @5
    @26
    @3
    fveq1
    fveq2d
    oveq1d
    mpteq2dv
    oveq2d
    evlslem1.e
    cS
    @12
    cgsu
    ovex
    fvmpt
    syl
    wph
    @13
    cS
    @18
    cgsu
    co
    @19
    wph
    @12
    @18
    cS
    cgsu
    wph
    vb
    cD
    @11
    @17
    wph
    @5
    cD
    wcel
    #
    wa
    #
    @7
    @16
    @10
    c.x
    @33
    @6
    @15
    cF
    @33
    @32
    @15
    cvv
    wcel
    #
    @6
    @15
    wceq
    wph
    @32
    simpr
    wph
    @34
    @32
    wph
    cH
    cK
    wcel
    c.0
    cvv
    wcel
    #
    @34
    evlslem3.q
    @35
    wph
    c.0
    cR
    c0g
    cfv
    cvv
    evlslem3.z
    cR
    c0g
    fvex
    eqeltri
    a1i
    @14
    cH
    c.0
    cK
    cvv
    ifexg
    syl2anc
    adantr
    vx
    @5
    @2
    @15
    cD
    cvv
    @3
    @0
    @5
    wceq
    @1
    @14
    cH
    c.0
    @0
    @5
    cA
    eqeq1
    ifbid
    @3
    eqid
    fvmptg
    syl2anc
    fveq2d
    oveq1d
    mpteq2dva
    oveq2d
    wph
    cD
    cC
    @18
    cS
    cvv
    cA
    cS
    c0g
    cfv
    #
    evlslem1.c
    @36
    eqid
    #
    wph
    cS
    crg
    wcel
    #
    cS
    cmnd
    wcel
    wph
    cS
    ccrg
    wcel
    #
    @38
    evlslem1.s
    cS
    crngring
    syl
    #
    cS
    ringmnd
    syl
    cD
    cvv
    wcel
    wph
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vh
    cn0
    cI
    cmap
    co
    cD
    evlslem1.d
    cn0
    cI
    cmap
    ovex
    rabex2
    a1i
    #
    evlslem3.k
    wph
    vb
    cD
    @17
    cC
    @18
    @33
    @38
    @16
    cC
    wcel
    #
    @10
    cC
    wcel
    #
    @17
    cC
    wcel
    wph
    @38
    @32
    @40
    adantr
    wph
    @42
    @32
    wph
    cK
    cC
    @15
    cF
    wph
    cF
    cR
    cS
    crh
    co
    wcel
    #
    cK
    cC
    cF
    wf
    evlslem1.f
    cK
    cC
    cR
    cS
    cF
    evlslem1.k
    evlslem1.c
    rhmf
    syl
    wph
    @14
    cH
    c.0
    cK
    evlslem3.q
    wph
    @24
    c.0
    cK
    wcel
    @25
    cK
    cR
    c.0
    evlslem1.k
    evlslem3.z
    ring0cl
    syl
    ifcld
    ffvelrnd
    adantr
    @33
    cI
    cC
    @9
    cT
    cvv
    cT
    c0g
    cfv
    #
    cC
    cS
    cT
    evlslem1.t
    evlslem1.c
    mgpbas
    #
    @45
    eqid
    #
    wph
    cT
    ccmn
    wcel
    #
    @32
    wph
    @39
    @48
    evlslem1.s
    cS
    cT
    evlslem1.t
    crngmgp
    syl
    #
    adantr
    wph
    cI
    cvv
    wcel
    #
    @32
    evlslem1.i
    adantr
    #
    @33
    vy
    vz
    cI
    cI
    cI
    c.ex
    cn0
    cC
    cC
    @5
    cG
    cvv
    cvv
    @33
    vy
    cv
    #
    cn0
    wcel
    #
    vz
    cv
    #
    cC
    wcel
    #
    wa
    #
    wa
    cT
    cmnd
    wcel
    #
    @53
    @55
    @52
    @54
    c.ex
    co
    cC
    wcel
    wph
    @57
    @32
    @56
    wph
    @48
    @57
    @49
    cT
    cmnmnd
    syl
    ad2antrr
    @33
    @53
    @55
    simprl
    @33
    @53
    @55
    simprr
    cC
    c.ex
    cT
    @52
    @54
    @46
    evlslem1.x
    mulgnn0cl
    syl3anc
    wph
    @50
    @32
    cI
    cn0
    @5
    wf
    #
    evlslem1.i
    cD
    vh
    @5
    cI
    cvv
    evlslem1.d
    psrbagf
    sylan
    #
    wph
    cI
    cC
    cG
    wf
    #
    @32
    evlslem1.g
    adantr
    #
    @51
    @51
    cI
    inidm
    off
    #
    @33
    @9
    cvv
    wcel
    #
    @9
    wfun
    @45
    cvv
    wcel
    #
    @5
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    @9
    @45
    csupp
    co
    @65
    wss
    @9
    @45
    cfsupp
    wbr
    @63
    @33
    @5
    cG
    @8
    ovex
    a1i
    @33
    cI
    cC
    @9
    @62
    ffund
    @64
    @33
    cT
    c0g
    fvex
    a1i
    wph
    @32
    @58
    @66
    wph
    @50
    @32
    @58
    @66
    wa
    wb
    evlslem1.i
    cD
    vh
    @5
    cI
    cvv
    evlslem1.d
    psrbag
    syl
    simplbda
    @33
    cI
    cC
    vy
    @9
    @65
    @45
    @62
    @33
    @52
    cI
    @65
    cdif
    wcel
    #
    wa
    #
    @52
    @9
    cfv
    #
    @52
    @5
    cfv
    #
    @52
    cG
    cfv
    #
    c.ex
    co
    #
    cc0
    @71
    c.ex
    co
    #
    @45
    @68
    @5
    cI
    wfn
    #
    cG
    cI
    wfn
    #
    @50
    @52
    cI
    wcel
    #
    @69
    @72
    wceq
    @33
    @74
    @67
    @33
    cI
    cn0
    @5
    @59
    ffnd
    #
    adantr
    wph
    @75
    @32
    @67
    wph
    cI
    cC
    cG
    evlslem1.g
    ffnd
    ad2antrr
    wph
    @50
    @32
    @67
    evlslem1.i
    ad2antrr
    @67
    @76
    @33
    @52
    cI
    @65
    eldifi
    #
    adantl
    cI
    c.ex
    @5
    cG
    cvv
    @52
    fnfvof
    syl22anc
    @68
    @70
    cc0
    @71
    c.ex
    @68
    @70
    cn
    wcel
    #
    wn
    @79
    @70
    cc0
    wceq
    #
    wo
    #
    @80
    @68
    @79
    @52
    @65
    wcel
    #
    @67
    @82
    wn
    @33
    @52
    cI
    @65
    eldifn
    adantl
    @68
    @79
    wa
    #
    @82
    @76
    @79
    @67
    @76
    @33
    @79
    @78
    ad2antlr
    @68
    @79
    simpr
    @83
    @74
    @82
    @76
    @79
    wa
    wb
    @33
    @74
    @67
    @79
    @77
    ad2antrr
    cI
    @52
    cn
    @5
    elpreima
    syl
    mpbir2and
    mtand
    @68
    @70
    cn0
    wcel
    #
    @81
    @33
    @58
    @76
    @84
    @67
    @59
    @78
    cI
    cn0
    @52
    @5
    ffvelrn
    syl2an
    @70
    elnn0
    sylib
    @79
    @80
    orel1
    sylc
    oveq1d
    @68
    @71
    cC
    wcel
    #
    @73
    @45
    wceq
    @33
    @60
    @76
    @85
    @67
    @61
    @78
    cI
    cC
    @52
    cG
    ffvelrn
    syl2an
    cC
    c.ex
    cT
    @71
    @45
    @46
    @47
    evlslem1.x
    mulg0
    syl
    3eqtrd
    suppss
    @65
    @9
    cvv
    cvv
    @45
    suppssfifsupp
    syl32anc
    gsumcl
    #
    cC
    cS
    c.x
    @16
    @10
    evlslem1.c
    evlslem1.m
    ringcl
    syl3anc
    @18
    eqid
    #
    fmptd
    wph
    cD
    @17
    vb
    cvv
    cA
    csn
    #
    @36
    wph
    @5
    cD
    @88
    cdif
    wcel
    #
    wa
    #
    @17
    @36
    @10
    c.x
    co
    #
    @36
    @90
    @16
    @36
    @10
    c.x
    @90
    @16
    c.0
    cF
    cfv
    #
    @36
    @90
    @15
    c.0
    cF
    @89
    @15
    c.0
    wceq
    wph
    @89
    @14
    cH
    c.0
    @89
    @5
    cA
    @5
    cD
    cA
    eldifsni
    neneqd
    iffalsed
    adantl
    fveq2d
    wph
    @92
    @36
    wceq
    #
    @89
    wph
    cF
    cR
    cS
    cghm
    co
    wcel
    #
    @93
    wph
    @44
    @94
    evlslem1.f
    cR
    cS
    cF
    rhmghm
    syl
    cR
    cS
    cF
    c.0
    @36
    evlslem3.z
    @37
    ghmid
    syl
    adantr
    eqtrd
    oveq1d
    @90
    @38
    @43
    @91
    @36
    wceq
    wph
    @38
    @89
    @40
    adantr
    @89
    wph
    @32
    @43
    @5
    cD
    @88
    eldifi
    @86
    sylan2
    cC
    cS
    c.x
    @10
    @36
    evlslem1.c
    evlslem1.m
    @37
    ringlz
    syl2anc
    eqtrd
    @41
    suppss2
    gsumpt
    eqtrd
    wph
    cA
    cD
    wcel
    @19
    @23
    wceq
    evlslem3.k
    vb
    cA
    @17
    @23
    cD
    @18
    @14
    @16
    @20
    @10
    @22
    c.x
    @14
    @15
    cH
    cF
    @14
    cH
    c.0
    iftrue
    fveq2d
    @14
    @9
    @21
    cT
    cgsu
    @5
    cA
    cG
    @8
    oveq1
    oveq2d
    oveq12d
    @87
    @20
    @22
    c.x
    ovex
    fvmpt
    syl
    3eqtrd
end
