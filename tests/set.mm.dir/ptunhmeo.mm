include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "wcel.mm"
include "ccnv.mm"
include "chmeo.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cun.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "cop.mm"
include "wceq.mm"
include "vex.mm"
include "op1std.mm"
include "op2ndd.mm"
include "uneq12d.mm"
include "mpt2mpt.mm"
include "eqtr4i.mm"
include "wa.mm"
include "wfn.mm"
include "cuni.mm"
include "cixp.mm"
include "cdif.mm"
include "wss.mm"
include "xp1st.mm"
include "adantl.mm"
include "cres.mm"
include "ixpeq2.mm"
include "fvres.mm"
include "unieqd.mm"
include "mprg.mm"
include "cvv.mm"
include "ctop.mm"
include "wf.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "ssexd.mm"
include "fssresd.mm"
include "ptuni.mm"
include "syl2anc.mm"
include "syl5eqr.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "xp2nd.mm"
include "eqcomd.mm"
include "cin.mm"
include "c0.mm"
include "wb.mm"
include "uneqdifeq.mm"
include "mpbid.mm"
include "ixpeq1d.mm"
include "ssun2.mm"
include "eqtrd.mm"
include "undifixp.mm"
include "syl3anc.mm"
include "ixpfn.mm"
include "syl.mm"
include "dffn5.mm"
include "sylib.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "ctopon.mm"
include "cpt.mm"
include "pttop.mm"
include "syl5eqel.mm"
include "toptopon.mm"
include "txtopon.mm"
include "wo.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "elun.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "fvun1.mm"
include "syl112anc.mm"
include "cnmpt1st.mm"
include "simpr.mm"
include "ptpjcn.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "fveq1.mm"
include "cnmpt11.mm"
include "eqeltrd.mm"
include "fvun2.mm"
include "cnmpt2nd.mm"
include "jaodan.mm"
include "syldan.mm"
include "ptcn.mm"
include "ptuncnv.mm"
include "eqid.mm"
include "ptrescn.mm"
include "cnmpt1t.mm"
include "ishmeo.mm"
include "sylanbrc.mm"

theorem ptunhmeo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cL: class L
  let cV: class V
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vw: setvar w
  let vz: setvar z
  assume ptunhmeo.x: |- X = U. K
  assume ptunhmeo.y: |- Y = U. L
  assume ptunhmeo.j: |- J = ( Xt_ ` F )
  assume ptunhmeo.k: |- K = ( Xt_ ` ( F |` A ) )
  assume ptunhmeo.l: |- L = ( Xt_ ` ( F |` B ) )
  assume ptunhmeo.g: |- G = ( x e. X , y e. Y |-> ( x u. y ) )
  assume ptunhmeo.c: |- ( ph -> C e. V )
  assume ptunhmeo.f: |- ( ph -> F : C --> Top )
  assume ptunhmeo.u: |- ( ph -> C = ( A u. B ) )
  assume ptunhmeo.i: |- ( ph -> ( A i^i B ) = (/) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  disjoint C x
  disjoint C y
  disjoint F x
  disjoint F y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint f k
  disjoint f n
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B f
  disjoint B k
  disjoint B n
  disjoint B w
  disjoint B z
  disjoint G z
  disjoint k ph
  disjoint ph w
  disjoint ph z
  disjoint C k
  disjoint C n
  disjoint C z
  disjoint F f
  disjoint F k
  disjoint F n
  disjoint F z
  disjoint J w
  disjoint J z
  disjoint K f
  disjoint K k
  disjoint K z
  disjoint L f
  disjoint L k
  disjoint L z
  disjoint V k
  disjoint V z
  disjoint X f
  disjoint X k
  disjoint X w
  disjoint X z
  disjoint Y f
  disjoint Y k
  disjoint Y w
  disjoint Y z
  assert |- ( ph -> G e. ( ( K tX L ) Homeo J ) )

  proof
    wph
    cG
    cK
    cL
    ctx
    co
    #
    cJ
    ccn
    co
    #
    wcel
    cG
    ccnv
    #
    cJ
    @0
    ccn
    co
    #
    wcel
    cG
    @0
    cJ
    chmeo
    co
    wcel
    wph
    cG
    vz
    cX
    cY
    cxp
    #
    vk
    cC
    vk
    cv
    #
    vz
    cv
    #
    c1st
    cfv
    #
    @6
    c2nd
    cfv
    #
    cun
    #
    cfv
    #
    cmpt
    #
    cmpt
    #
    @1
    wph
    cG
    vz
    @4
    @9
    cmpt
    #
    @12
    cG
    vx
    vy
    cX
    cY
    vx
    cv
    #
    vy
    cv
    #
    cun
    #
    cmpt2
    @13
    ptunhmeo.g
    vx
    vy
    vz
    cX
    cY
    @9
    @16
    @6
    @14
    @15
    cop
    wceq
    @7
    @14
    @8
    @15
    @14
    @15
    @6
    vx
    vex
    #
    vy
    vex
    #
    op1std
    #
    @14
    @15
    @6
    @17
    @18
    op2ndd
    #
    uneq12d
    mpt2mpt
    eqtr4i
    wph
    vz
    @4
    @9
    @11
    wph
    @6
    @4
    wcel
    #
    wa
    #
    @9
    cC
    wfn
    #
    @9
    @11
    wceq
    @22
    @9
    vn
    cC
    vn
    cv
    #
    cF
    cfv
    #
    cuni
    #
    cixp
    wcel
    #
    @23
    @22
    @7
    vn
    cA
    @26
    cixp
    #
    wcel
    #
    @8
    vn
    cC
    cA
    cdif
    #
    @26
    cixp
    #
    wcel
    cA
    cC
    wss
    #
    @27
    @22
    @7
    cX
    @28
    @21
    @7
    cX
    wcel
    wph
    @6
    cX
    cY
    xp1st
    adantl
    wph
    @28
    cX
    wceq
    @21
    wph
    @28
    cK
    cuni
    #
    cX
    wph
    @28
    vn
    cA
    @24
    cF
    cA
    cres
    #
    cfv
    #
    cuni
    #
    cixp
    #
    @33
    @36
    @26
    wceq
    @37
    @28
    wceq
    vn
    cA
    vn
    cA
    @36
    @26
    ixpeq2
    @24
    cA
    wcel
    @35
    @25
    @24
    cA
    cF
    fvres
    unieqd
    mprg
    wph
    cA
    cvv
    wcel
    #
    cA
    ctop
    @34
    wf
    #
    @37
    @33
    wceq
    wph
    cA
    cC
    cV
    ptunhmeo.c
    wph
    cA
    cB
    cun
    #
    cA
    cC
    cA
    cB
    ssun1
    ptunhmeo.u
    syl5sseqr
    #
    ssexd
    #
    wph
    cC
    ctop
    cA
    cF
    ptunhmeo.f
    @41
    fssresd
    #
    vn
    cA
    @34
    cK
    cvv
    ptunhmeo.k
    ptuni
    syl2anc
    syl5eqr
    ptunhmeo.x
    syl6eqr
    adantr
    eleqtrrd
    #
    @22
    @8
    cY
    @31
    @21
    @8
    cY
    wcel
    wph
    @6
    cX
    cY
    xp2nd
    adantl
    #
    wph
    @31
    cY
    wceq
    @21
    wph
    @31
    vn
    cB
    @26
    cixp
    #
    cY
    wph
    vn
    @30
    cB
    @26
    wph
    @40
    cC
    wceq
    #
    @30
    cB
    wceq
    #
    wph
    cC
    @40
    ptunhmeo.u
    eqcomd
    wph
    @32
    cA
    cB
    cin
    c0
    wceq
    #
    @47
    @48
    wb
    @41
    ptunhmeo.i
    cA
    cB
    cC
    uneqdifeq
    syl2anc
    mpbid
    ixpeq1d
    wph
    @46
    cL
    cuni
    #
    cY
    wph
    @46
    vn
    cB
    @24
    cF
    cB
    cres
    #
    cfv
    #
    cuni
    #
    cixp
    #
    @50
    @53
    @26
    wceq
    @54
    @46
    wceq
    vn
    cB
    vn
    cB
    @53
    @26
    ixpeq2
    @24
    cB
    wcel
    @52
    @25
    @24
    cB
    cF
    fvres
    unieqd
    mprg
    wph
    cB
    cvv
    wcel
    #
    cB
    ctop
    @51
    wf
    #
    @54
    @50
    wceq
    wph
    cB
    cC
    cV
    ptunhmeo.c
    wph
    @40
    cB
    cC
    cB
    cA
    ssun2
    ptunhmeo.u
    syl5sseqr
    #
    ssexd
    #
    wph
    cC
    ctop
    cB
    cF
    ptunhmeo.f
    @57
    fssresd
    #
    vn
    cB
    @51
    cL
    cvv
    ptunhmeo.l
    ptuni
    syl2anc
    syl5eqr
    ptunhmeo.y
    syl6eqr
    #
    eqtrd
    adantr
    eleqtrrd
    wph
    @32
    @21
    @41
    adantr
    vn
    cC
    cA
    @26
    @7
    @8
    undifixp
    syl3anc
    vn
    cC
    @26
    @9
    ixpfn
    syl
    vk
    cC
    @9
    dffn5
    sylib
    mpteq2dva
    syl5eq
    wph
    vz
    @10
    vk
    cF
    cC
    @0
    cJ
    cV
    @4
    ptunhmeo.j
    wph
    cK
    cX
    ctopon
    cfv
    wcel
    #
    cL
    cY
    ctopon
    cfv
    wcel
    #
    @0
    @4
    ctopon
    cfv
    wcel
    #
    wph
    cK
    ctop
    wcel
    @61
    wph
    cK
    @34
    cpt
    cfv
    #
    ctop
    ptunhmeo.k
    wph
    @38
    @39
    @64
    ctop
    wcel
    @42
    @43
    cA
    @34
    cvv
    pttop
    syl2anc
    syl5eqel
    cK
    cX
    ptunhmeo.x
    toptopon
    sylib
    #
    wph
    cL
    ctop
    wcel
    @62
    wph
    cL
    @51
    cpt
    cfv
    #
    ctop
    ptunhmeo.l
    wph
    @55
    @56
    @66
    ctop
    wcel
    @58
    @59
    cB
    @51
    cvv
    pttop
    syl2anc
    syl5eqel
    cL
    cY
    ptunhmeo.y
    toptopon
    sylib
    #
    cK
    cL
    cX
    cY
    txtopon
    syl2anc
    #
    ptunhmeo.c
    ptunhmeo.f
    wph
    @5
    cC
    wcel
    #
    @5
    cA
    wcel
    #
    @5
    cB
    wcel
    #
    wo
    #
    vz
    @4
    @10
    cmpt
    #
    @0
    @5
    cF
    cfv
    #
    ccn
    co
    #
    wcel
    #
    wph
    @69
    wa
    @5
    @40
    wcel
    #
    @72
    wph
    @69
    @77
    wph
    cC
    @40
    @5
    ptunhmeo.u
    eleq2d
    biimpa
    @5
    cA
    cB
    elun
    sylib
    wph
    @70
    @76
    @71
    wph
    @70
    wa
    #
    @73
    vz
    @4
    @5
    @7
    cfv
    #
    cmpt
    @75
    @78
    vz
    @4
    @10
    @79
    @78
    @21
    wa
    @7
    cA
    wfn
    #
    @8
    cB
    wfn
    #
    @49
    @70
    @10
    @79
    wceq
    wph
    @21
    @80
    @70
    @22
    @29
    @80
    @44
    vn
    cA
    @26
    @7
    ixpfn
    syl
    #
    adantlr
    wph
    @21
    @81
    @70
    @22
    @8
    @46
    wcel
    @81
    @22
    @8
    cY
    @46
    @45
    wph
    @46
    cY
    wceq
    @21
    @60
    adantr
    eleqtrrd
    vn
    cB
    @26
    @8
    ixpfn
    syl
    #
    adantlr
    wph
    @49
    @70
    @21
    ptunhmeo.i
    ad2antrr
    wph
    @70
    @21
    simplr
    cA
    cB
    @7
    @8
    @5
    fvun1
    syl112anc
    mpteq2dva
    @78
    vz
    vf
    @7
    @5
    vf
    cv
    #
    cfv
    #
    @79
    @0
    cK
    @74
    @4
    cX
    wph
    @63
    @70
    @68
    adantr
    @78
    vz
    @4
    @7
    cmpt
    vx
    vy
    cX
    cY
    @14
    cmpt2
    @0
    cK
    ccn
    co
    vx
    vy
    vz
    cX
    cY
    @7
    @14
    @19
    mpt2mpt
    @78
    vx
    vy
    cK
    cL
    cX
    cY
    wph
    @61
    @70
    @65
    adantr
    #
    wph
    @62
    @70
    @67
    adantr
    cnmpt1st
    syl5eqel
    @86
    @78
    vf
    cX
    @85
    cmpt
    #
    cK
    @5
    @34
    cfv
    #
    ccn
    co
    #
    cK
    @74
    ccn
    co
    @78
    @38
    @39
    @70
    @87
    @89
    wcel
    wph
    @38
    @70
    @42
    adantr
    wph
    @39
    @70
    @43
    adantr
    wph
    @70
    simpr
    vf
    cA
    @34
    @5
    cK
    cvv
    cX
    ptunhmeo.x
    ptunhmeo.k
    ptpjcn
    syl3anc
    @78
    @88
    @74
    cK
    ccn
    @70
    @88
    @74
    wceq
    wph
    @5
    cA
    cF
    fvres
    adantl
    oveq2d
    eleqtrd
    @5
    @84
    @7
    fveq1
    cnmpt11
    eqeltrd
    wph
    @71
    wa
    #
    @73
    vz
    @4
    @5
    @8
    cfv
    #
    cmpt
    @75
    @90
    vz
    @4
    @10
    @91
    @90
    @21
    wa
    @80
    @81
    @49
    @71
    @10
    @91
    wceq
    wph
    @21
    @80
    @71
    @82
    adantlr
    wph
    @21
    @81
    @71
    @83
    adantlr
    wph
    @49
    @71
    @21
    ptunhmeo.i
    ad2antrr
    wph
    @71
    @21
    simplr
    cA
    cB
    @7
    @8
    @5
    fvun2
    syl112anc
    mpteq2dva
    @90
    vz
    vf
    @8
    @85
    @91
    @0
    cL
    @74
    @4
    cY
    wph
    @63
    @71
    @68
    adantr
    @90
    vz
    @4
    @8
    cmpt
    vx
    vy
    cX
    cY
    @15
    cmpt2
    @0
    cL
    ccn
    co
    vx
    vy
    vz
    cX
    cY
    @8
    @15
    @20
    mpt2mpt
    @90
    vx
    vy
    cK
    cL
    cX
    cY
    wph
    @61
    @71
    @65
    adantr
    wph
    @62
    @71
    @67
    adantr
    #
    cnmpt2nd
    syl5eqel
    @92
    @90
    vf
    cY
    @85
    cmpt
    #
    cL
    @5
    @51
    cfv
    #
    ccn
    co
    #
    cL
    @74
    ccn
    co
    @90
    @55
    @56
    @71
    @93
    @95
    wcel
    wph
    @55
    @71
    @58
    adantr
    wph
    @56
    @71
    @59
    adantr
    wph
    @71
    simpr
    vf
    cB
    @51
    @5
    cL
    cvv
    cY
    ptunhmeo.y
    ptunhmeo.l
    ptpjcn
    syl3anc
    @90
    @94
    @74
    cL
    ccn
    @71
    @94
    @74
    wceq
    wph
    @5
    cB
    cF
    fvres
    adantl
    oveq2d
    eleqtrd
    @5
    @84
    @8
    fveq1
    cnmpt11
    eqeltrd
    jaodan
    syldan
    ptcn
    eqeltrd
    wph
    @2
    vz
    cJ
    cuni
    #
    @6
    cA
    cres
    #
    @6
    cB
    cres
    #
    cop
    cmpt
    @3
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    cF
    cG
    cJ
    cK
    cL
    cV
    cX
    cY
    ptunhmeo.x
    ptunhmeo.y
    ptunhmeo.j
    ptunhmeo.k
    ptunhmeo.l
    ptunhmeo.g
    ptunhmeo.c
    ptunhmeo.f
    ptunhmeo.u
    ptunhmeo.i
    ptuncnv
    wph
    vz
    @97
    @98
    cJ
    cK
    cL
    @96
    wph
    cJ
    ctop
    wcel
    cJ
    @96
    ctopon
    cfv
    wcel
    wph
    cJ
    cF
    cpt
    cfv
    #
    ctop
    ptunhmeo.j
    wph
    cC
    cV
    wcel
    #
    cC
    ctop
    cF
    wf
    #
    @99
    ctop
    wcel
    ptunhmeo.c
    ptunhmeo.f
    cC
    cF
    cV
    pttop
    syl2anc
    syl5eqel
    cJ
    @96
    @96
    eqid
    #
    toptopon
    sylib
    wph
    @100
    @101
    @32
    vz
    @96
    @97
    cmpt
    cJ
    cK
    ccn
    co
    wcel
    ptunhmeo.c
    ptunhmeo.f
    @41
    vz
    cC
    cA
    cF
    cJ
    cK
    cV
    @96
    @102
    ptunhmeo.j
    ptunhmeo.k
    ptrescn
    syl3anc
    wph
    @100
    @101
    cB
    cC
    wss
    vz
    @96
    @98
    cmpt
    cJ
    cL
    ccn
    co
    wcel
    ptunhmeo.c
    ptunhmeo.f
    @57
    vz
    cC
    cB
    cF
    cJ
    cL
    cV
    @96
    @102
    ptunhmeo.j
    ptunhmeo.l
    ptrescn
    syl3anc
    cnmpt1t
    eqeltrd
    cG
    @0
    cJ
    ishmeo
    sylanbrc
end
