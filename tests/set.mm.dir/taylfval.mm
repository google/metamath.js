include "ctayl.mm"
include "co.mm"
include "cc.mm"
include "cv.mm"
include "csn.mm"
include "ccnfld.mm"
include "cc0.mm"
include "cicc.mm"
include "cz.mm"
include "cin.mm"
include "cdvn.mm"
include "cfv.mm"
include "cfa.mm"
include "cdiv.mm"
include "cmin.mm"
include "cexp.mm"
include "cmul.mm"
include "cmpt.mm"
include "ctsu.mm"
include "cxp.mm"
include "ciun.mm"
include "cn0.mm"
include "cpnf.mm"
include "cun.mm"
include "cdm.mm"
include "ciin.mm"
include "cvv.mm"
include "cr.mm"
include "cpr.mm"
include "cpm.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-tayl.mm"
include "a1i.mm"
include "wa.mm"
include "eqidd.mm"
include "wcel.mm"
include "oveq12.mm"
include "ad2antlr.mm"
include "fveq1d.mm"
include "dmeqd.mm"
include "iineq2dv.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "xpeq2d.mm"
include "iuneq2d.mm"
include "mpt2eq123dv.mm"
include "simpr.mm"
include "wf.mm"
include "wss.mm"
include "cnex.mm"
include "elpm2r.mm"
include "syl22anc.mm"
include "wral.mm"
include "nn0ex.mm"
include "snex.mm"
include "unex.mm"
include "c0.mm"
include "wne.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "0xr.mm"
include "nn0ssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "pnfxr.mm"
include "snssi.mm"
include "ax-mp.mm"
include "unssi.mm"
include "sseli.mm"
include "wo.mm"
include "elun.mm"
include "nn0ge0.mm"
include "0lepnf.mm"
include "elsni.mm"
include "syl5breqr.mm"
include "jaoi.mm"
include "sylbi.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "0z.mm"
include "inelcm.mm"
include "sylancl.mm"
include "fvex.mm"
include "dmex.mm"
include "rgenw.mm"
include "iinexg.mm"
include "rgen.mm"
include "eqid.mm"
include "mpt2exxg.mm"
include "mp2an.mm"
include "ovmpt2dx.mm"
include "simprl.mm"
include "ineq1d.mm"
include "simprr.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "mpteq12dv.mm"
include "iineq1.mm"
include "syl.mm"
include "pnfex.mm"
include "elsn2.mm"
include "orbi2i.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "wrex.mm"
include "wb.mm"
include "oveq2.mm"
include "neeq1d.mm"
include "vtoclga.mm"
include "r19.2z.mm"
include "syl2anc.mm"
include "elex.mm"
include "rexlimivw.mm"
include "eliin.mm"
include "3syl.mm"
include "mpbird.mm"
include "adantl.mm"
include "taylfvallem.mm"
include "xpss12.mm"
include "iunss.mm"
include "xpex.mm"
include "ssex.mm"
include "syl5eq.mm"

theorem taylfval
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cF: class F
  let cN: class N
  let va: setvar a
  let vn: setvar n
  let vy: setvar y
  let vf: setvar f
  let vs: setvar s
  let cY: class Y
  let cX: class X
  assume taylfval.s: |- ( ph -> S e. { RR , CC } )
  assume taylfval.f: |- ( ph -> F : A --> CC )
  assume taylfval.a: |- ( ph -> A C_ S )
  assume taylfval.n: |- ( ph -> ( N e. NN0 \/ N = +oo ) )
  assume taylfval.b: |- ( ( ph /\ k e. ( ( 0 [,] N ) i^i ZZ ) ) -> B e. dom ( ( S Dn F ) ` k ) )
  assume taylfval.t: |- T = ( N ( S Tayl F ) B )

  disjoint k x
  disjoint B k
  disjoint B x
  disjoint F k
  disjoint F x
  disjoint k ph
  disjoint ph x
  disjoint N k
  disjoint N x
  disjoint S k
  disjoint S x
  disjoint T x
  disjoint a k
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint k n
  disjoint k y
  disjoint n x
  disjoint n y
  disjoint B n
  disjoint x y
  disjoint B y
  disjoint a f
  disjoint a s
  disjoint F a
  disjoint f k
  disjoint f n
  disjoint f s
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint k s
  disjoint n s
  disjoint F n
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint F y
  disjoint a ph
  disjoint f ph
  disjoint n ph
  disjoint ph s
  disjoint ph y
  disjoint Y x
  disjoint N a
  disjoint N n
  disjoint N y
  disjoint S a
  disjoint S f
  disjoint S n
  disjoint S s
  disjoint S y
  disjoint T y
  disjoint X k
  disjoint X x
  assert |- ( ph -> T = U_ x e. CC ( { x } X. ( CCfld tsums ( k e. ( ( 0 [,] N ) i^i ZZ ) |-> ( ( ( ( ( S Dn F ) ` k ) ` B ) / ( ! ` k ) ) x. ( ( x - B ) ^ k ) ) ) ) ) )

  proof
    wph
    cT
    cN
    cB
    cS
    cF
    ctayl
    co
    #
    co
    vx
    cc
    vx
    cv
    #
    csn
    #
    ccnfld
    vk
    cc0
    cN
    cicc
    co
    #
    cz
    cin
    #
    cB
    vk
    cv
    #
    cS
    cF
    cdvn
    co
    #
    cfv
    #
    cfv
    #
    @5
    cfa
    cfv
    #
    cdiv
    co
    #
    @1
    cB
    cmin
    co
    #
    @5
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    ctsu
    co
    #
    cxp
    #
    ciun
    #
    taylfval.t
    wph
    vn
    va
    cN
    cB
    cn0
    cpnf
    csn
    #
    cun
    #
    vk
    cc0
    vn
    cv
    #
    cicc
    co
    #
    cz
    cin
    #
    @7
    cdm
    #
    ciin
    #
    vx
    cc
    @2
    ccnfld
    vk
    @22
    va
    cv
    #
    @7
    cfv
    #
    @9
    cdiv
    co
    #
    @1
    @25
    cmin
    co
    #
    @5
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    ctsu
    co
    #
    cxp
    #
    ciun
    #
    @17
    @0
    vk
    @4
    @23
    ciin
    #
    cvv
    wph
    vs
    vf
    cS
    cF
    cr
    cc
    cpr
    #
    cc
    vs
    cv
    #
    cpm
    co
    #
    vn
    va
    @19
    vk
    @22
    @5
    @37
    vf
    cv
    #
    cdvn
    co
    #
    cfv
    #
    cdm
    #
    ciin
    #
    vx
    cc
    @2
    ccnfld
    vk
    @22
    @25
    @41
    cfv
    #
    @9
    cdiv
    co
    #
    @29
    cmul
    co
    #
    cmpt
    #
    ctsu
    co
    #
    cxp
    #
    ciun
    #
    cmpt2
    #
    vn
    va
    @19
    @24
    @34
    cmpt2
    #
    ctayl
    cc
    cS
    cpm
    co
    #
    cvv
    ctayl
    vs
    vf
    @36
    @38
    @51
    cmpt2
    wceq
    wph
    vx
    vf
    vk
    vn
    vs
    va
    df-tayl
    a1i
    wph
    @37
    cS
    wceq
    #
    @39
    cF
    wceq
    wa
    #
    wa
    #
    vn
    va
    @19
    @43
    @50
    @19
    @24
    @34
    @56
    @19
    eqidd
    @56
    vk
    @22
    @42
    @23
    @56
    @5
    @22
    wcel
    #
    wa
    #
    @41
    @7
    @58
    @5
    @40
    @6
    @55
    @40
    @6
    wceq
    wph
    @57
    @37
    cS
    @39
    cF
    cdvn
    oveq12
    ad2antlr
    fveq1d
    #
    dmeqd
    iineq2dv
    @56
    vx
    cc
    @49
    @33
    @56
    @48
    @32
    @2
    @56
    @47
    @31
    ccnfld
    ctsu
    @56
    vk
    @22
    @46
    @30
    @58
    @45
    @27
    @29
    cmul
    @58
    @44
    @26
    @9
    cdiv
    @58
    @25
    @41
    @7
    @59
    fveq1d
    oveq1d
    oveq1d
    mpteq2dva
    oveq2d
    xpeq2d
    iuneq2d
    mpt2eq123dv
    wph
    @54
    wa
    @37
    cS
    cc
    cpm
    wph
    @54
    simpr
    oveq2d
    taylfval.s
    wph
    cc
    cvv
    wcel
    #
    cS
    @36
    wcel
    cA
    cc
    cF
    wf
    cA
    cS
    wss
    cF
    @53
    wcel
    @60
    wph
    cnex
    a1i
    taylfval.s
    taylfval.f
    taylfval.a
    cc
    cS
    cA
    cF
    cvv
    @36
    elpm2r
    syl22anc
    @52
    cvv
    wcel
    #
    wph
    @19
    cvv
    wcel
    @24
    cvv
    wcel
    #
    vn
    @19
    wral
    @61
    cn0
    @18
    nn0ex
    cpnf
    snex
    unex
    @62
    vn
    @19
    @20
    @19
    wcel
    #
    @22
    c0
    wne
    #
    @23
    cvv
    wcel
    #
    vk
    @22
    wral
    @62
    @63
    cc0
    @21
    wcel
    #
    cc0
    cz
    wcel
    @64
    @63
    cc0
    cxr
    wcel
    #
    @20
    cxr
    wcel
    cc0
    @20
    cle
    wbr
    #
    @66
    @67
    @63
    0xr
    a1i
    @19
    cxr
    @20
    cn0
    @18
    cxr
    cn0
    cr
    cxr
    nn0ssre
    ressxr
    sstri
    cpnf
    cxr
    wcel
    @18
    cxr
    wss
    pnfxr
    cpnf
    cxr
    snssi
    ax-mp
    unssi
    sseli
    @63
    @20
    cn0
    wcel
    #
    @20
    @18
    wcel
    #
    wo
    @68
    @20
    cn0
    @18
    elun
    @69
    @68
    @70
    @20
    nn0ge0
    @70
    cc0
    cpnf
    @20
    cle
    0lepnf
    @20
    cpnf
    elsni
    syl5breqr
    jaoi
    sylbi
    cc0
    @20
    lbicc2
    syl3anc
    0z
    cc0
    @21
    cz
    inelcm
    sylancl
    #
    @65
    vk
    @22
    @7
    @5
    @6
    fvex
    dmex
    rgenw
    vk
    @22
    @23
    cvv
    iinexg
    sylancl
    rgen
    vn
    va
    @19
    @24
    @34
    cvv
    cvv
    @52
    @52
    eqid
    mpt2exxg
    mp2an
    a1i
    ovmpt2dx
    wph
    @20
    cN
    wceq
    #
    @25
    cB
    wceq
    #
    wa
    wa
    #
    vx
    cc
    @33
    @16
    @74
    @32
    @15
    @2
    @74
    @31
    @14
    ccnfld
    ctsu
    @74
    vk
    @22
    @30
    @4
    @13
    @74
    @21
    @3
    cz
    @74
    @20
    cN
    cc0
    cicc
    wph
    @72
    @73
    simprl
    oveq2d
    ineq1d
    @74
    @27
    @10
    @29
    @12
    cmul
    @74
    @26
    @8
    @9
    cdiv
    @74
    @25
    cB
    @7
    wph
    @72
    @73
    simprr
    #
    fveq2d
    oveq1d
    @74
    @28
    @11
    @5
    cexp
    @74
    @25
    cB
    @1
    cmin
    @75
    oveq2d
    oveq1d
    oveq12d
    mpteq12dv
    oveq2d
    xpeq2d
    iuneq2d
    wph
    @72
    wa
    #
    @22
    @4
    wceq
    @24
    @35
    wceq
    @76
    @21
    @3
    cz
    @76
    @20
    cN
    cc0
    cicc
    wph
    @72
    simpr
    oveq2d
    ineq1d
    vk
    @22
    @4
    @23
    iineq1
    syl
    wph
    cN
    cn0
    wcel
    #
    cN
    @18
    wcel
    #
    wo
    #
    cN
    @19
    wcel
    #
    wph
    @77
    cN
    cpnf
    wceq
    #
    wo
    @79
    taylfval.n
    @78
    @81
    @77
    cN
    cpnf
    pnfex
    elsn2
    orbi2i
    sylibr
    cN
    cn0
    @18
    elun
    sylibr
    #
    wph
    cB
    @35
    wcel
    #
    cB
    @23
    wcel
    #
    vk
    @4
    wral
    #
    wph
    @84
    vk
    @4
    taylfval.b
    ralrimiva
    #
    wph
    @84
    vk
    @4
    wrex
    #
    cB
    cvv
    wcel
    #
    @83
    @85
    wb
    wph
    @4
    c0
    wne
    #
    @85
    @87
    wph
    @80
    @89
    @82
    @64
    @89
    vn
    cN
    @19
    @72
    @22
    @4
    c0
    @72
    @21
    @3
    cz
    @20
    cN
    cc0
    cicc
    oveq2
    ineq1d
    neeq1d
    @71
    vtoclga
    syl
    @86
    @84
    vk
    @4
    r19.2z
    syl2anc
    @84
    @88
    vk
    @4
    cB
    @23
    elex
    rexlimivw
    vk
    cB
    @4
    @23
    cvv
    eliin
    3syl
    mpbird
    wph
    @17
    cc
    cc
    cxp
    #
    wss
    #
    @17
    cvv
    wcel
    wph
    @16
    @90
    wss
    #
    vx
    cc
    wral
    @91
    wph
    @92
    vx
    cc
    wph
    @1
    cc
    wcel
    #
    wa
    @2
    cc
    wss
    #
    @15
    cc
    wss
    @92
    @93
    @94
    wph
    @1
    cc
    snssi
    adantl
    wph
    cA
    cB
    cS
    vk
    cF
    cN
    @1
    taylfval.s
    taylfval.f
    taylfval.a
    taylfval.n
    taylfval.b
    taylfvallem
    @2
    cc
    @15
    cc
    xpss12
    syl2anc
    ralrimiva
    vx
    cc
    @16
    @90
    iunss
    sylibr
    @17
    @90
    cc
    cc
    cnex
    cnex
    xpex
    ssex
    syl
    ovmpt2dx
    syl5eq
end
