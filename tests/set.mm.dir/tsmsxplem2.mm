include "cxp.mm"
include "cres.mm"
include "cgsu.mm"
include "co.mm"
include "cabl.mm"
include "wcel.mm"
include "wceq.mm"
include "cgrp.mm"
include "ccmn.mm"
include "ctgp.mm"
include "tgpgrp.mm"
include "syl.mm"
include "isabl.mm"
include "sylanbrc.mm"
include "cfn.mm"
include "cpw.mm"
include "cin.mm"
include "wss.mm"
include "elfpw.mm"
include "simprbi.mm"
include "xpfi.mm"
include "syl2anc.mm"
include "simplbi.mm"
include "xpss12.mm"
include "fssresd.mm"
include "fdmfifsupp.mm"
include "gsumcl.mm"
include "ablpncan3.mm"
include "syl12anc.mm"
include "cv.mm"
include "wral.mm"
include "cfv.mm"
include "csn.mm"
include "cmpt.mm"
include "cof.mm"
include "wa.mm"
include "adantr.mm"
include "snfi.mm"
include "sylancr.mm"
include "wf.mm"
include "sselda.mm"
include "snssd.mm"
include "cvv.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "eqid.mm"
include "fmptd.mm"
include "ovexd.mm"
include "fsuppmptdm.mm"
include "gsumsub.mm"
include "fvexd.mm"
include "feqresmpt.mm"
include "eqidd.mm"
include "offval2.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "simpr.mm"
include "fovrnd.mm"
include "weq.mm"
include "velsn.mm"
include "ovres.mm"
include "sylanbr.mm"
include "oveq1.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "gsumsn.mm"
include "syl3anc.mm"
include "gsumxp.mm"
include "adantll.mm"
include "3eqtr4d.mm"
include "eqtr4d.mm"
include "3eqtr3d.mm"
include "cmap.mm"
include "fveq2.mm"
include "sneq.mm"
include "xpeq1d.mm"
include "reseq2d.mm"
include "oveq12d.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "elmapd.mm"
include "mpbird.mm"
include "oveq2.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqeltrrd.mm"
include "rspc2va.mm"
include "syl21anc.mm"

theorem tsmsxplem2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cS: class S
  let cT: class T
  let cU: class U
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vc: setvar c
  let vd: setvar d
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vh: setvar h
  let vn: setvar n
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  assume tsmsxp.b: |- B = ( Base ` G )
  assume tsmsxp.g: |- ( ph -> G e. CMnd )
  assume tsmsxp.2: |- ( ph -> G e. TopGrp )
  assume tsmsxp.a: |- ( ph -> A e. V )
  assume tsmsxp.c: |- ( ph -> C e. W )
  assume tsmsxp.f: |- ( ph -> F : ( A X. C ) --> B )
  assume tsmsxp.h: |- ( ph -> H : A --> B )
  assume tsmsxp.1: |- ( ( ph /\ j e. A ) -> ( H ` j ) e. ( G tsums ( k e. C |-> ( j F k ) ) ) )
  assume tsmsxp.j: |- J = ( TopOpen ` G )
  assume tsmsxp.z: |- .0. = ( 0g ` G )
  assume tsmsxp.p: |- .+ = ( +g ` G )
  assume tsmsxp.m: |- .- = ( -g ` G )
  assume tsmsxp.l: |- ( ph -> L e. J )
  assume tsmsxp.3: |- ( ph -> .0. e. L )
  assume tsmsxp.k: |- ( ph -> K e. ( ~P A i^i Fin ) )
  assume tsmsxp.4: |- ( ph -> A. c e. S A. d e. T ( c .+ d ) e. U )
  assume tsmsxp.n: |- ( ph -> N e. ( ~P C i^i Fin ) )
  assume tsmsxp.s: |- ( ph -> D C_ ( K X. N ) )
  assume tsmsxp.x: |- ( ph -> A. x e. K ( ( H ` x ) .- ( G gsum ( F |` ( { x } X. N ) ) ) ) e. L )
  assume tsmsxp.5: |- ( ph -> ( G gsum ( F |` ( K X. N ) ) ) e. S )
  assume tsmsxp.6: |- ( ph -> A. g e. ( L ^m K ) ( G gsum g ) e. T )

  disjoint g k
  disjoint .0. g
  disjoint .0. k
  disjoint c d
  disjoint c g
  disjoint c j
  disjoint c k
  disjoint c x
  disjoint G c
  disjoint d g
  disjoint d j
  disjoint d k
  disjoint d x
  disjoint G d
  disjoint g j
  disjoint g x
  disjoint G g
  disjoint j k
  disjoint j x
  disjoint G j
  disjoint k x
  disjoint G k
  disjoint G x
  disjoint B g
  disjoint B k
  disjoint D g
  disjoint D j
  disjoint D k
  disjoint D x
  disjoint L g
  disjoint L j
  disjoint L x
  disjoint A g
  disjoint A j
  disjoint A k
  disjoint K c
  disjoint K d
  disjoint K g
  disjoint K j
  disjoint K k
  disjoint K x
  disjoint S c
  disjoint H d
  disjoint H g
  disjoint H j
  disjoint H k
  disjoint H x
  disjoint N c
  disjoint N d
  disjoint N g
  disjoint N x
  disjoint U c
  disjoint U d
  disjoint .- d
  disjoint .- g
  disjoint .- j
  disjoint .- x
  disjoint C g
  disjoint C j
  disjoint C k
  disjoint T c
  disjoint T d
  disjoint T g
  disjoint .+ c
  disjoint .+ d
  disjoint .+ g
  disjoint F c
  disjoint F d
  disjoint F g
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint g ph
  disjoint j ph
  disjoint k ph
  disjoint g w
  disjoint g y
  disjoint g z
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint w y
  disjoint w z
  disjoint .0. w
  disjoint y z
  disjoint .0. y
  disjoint .0. z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a j
  disjoint a k
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint G a
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b j
  disjoint b k
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint G b
  disjoint c f
  disjoint c h
  disjoint c n
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint d f
  disjoint d h
  disjoint d n
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint f g
  disjoint f h
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint G f
  disjoint g h
  disjoint g n
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint h j
  disjoint h k
  disjoint h n
  disjoint h s
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint G h
  disjoint j n
  disjoint j s
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j y
  disjoint j z
  disjoint k n
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint G n
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint G t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint G v
  disjoint w x
  disjoint G w
  disjoint x y
  disjoint x z
  disjoint G y
  disjoint G z
  disjoint J y
  disjoint B b
  disjoint B h
  disjoint B s
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint D f
  disjoint D n
  disjoint D y
  disjoint D z
  disjoint L f
  disjoint L n
  disjoint L y
  disjoint L z
  disjoint A a
  disjoint A b
  disjoint A h
  disjoint A n
  disjoint A s
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A y
  disjoint A z
  disjoint K f
  disjoint K n
  disjoint K w
  disjoint K y
  disjoint K z
  disjoint H a
  disjoint H b
  disjoint H f
  disjoint H h
  disjoint H n
  disjoint H s
  disjoint H t
  disjoint H u
  disjoint H v
  disjoint H y
  disjoint H z
  disjoint N w
  disjoint N y
  disjoint N z
  disjoint .- f
  disjoint .- n
  disjoint .- y
  disjoint .- z
  disjoint C b
  disjoint C f
  disjoint C h
  disjoint C n
  disjoint C s
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C y
  disjoint C z
  disjoint .+ y
  disjoint F b
  disjoint F f
  disjoint F h
  disjoint F n
  disjoint F s
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint a ph
  disjoint b ph
  disjoint f ph
  disjoint h ph
  disjoint n ph
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( G gsum ( H |` K ) ) e. U )

  proof
    wph
    cG
    cF
    cK
    cN
    cxp
    #
    cres
    #
    cgsu
    co
    #
    cG
    cH
    cK
    cres
    #
    cgsu
    co
    #
    @2
    c.mi
    co
    #
    c.pl
    co
    #
    @4
    cU
    wph
    cG
    cabl
    wcel
    #
    @2
    cB
    wcel
    @4
    cB
    wcel
    @6
    @4
    wceq
    wph
    cG
    cgrp
    wcel
    #
    cG
    ccmn
    wcel
    #
    @7
    wph
    cG
    ctgp
    wcel
    @8
    tsmsxp.2
    cG
    tgpgrp
    syl
    tsmsxp.g
    cG
    isabl
    sylanbrc
    #
    wph
    @0
    cB
    @1
    cG
    cfn
    c.0
    tsmsxp.b
    tsmsxp.z
    tsmsxp.g
    wph
    cK
    cfn
    wcel
    #
    cN
    cfn
    wcel
    #
    @0
    cfn
    wcel
    wph
    cK
    cA
    cpw
    cfn
    cin
    #
    wcel
    #
    @11
    tsmsxp.k
    @14
    cK
    cA
    wss
    #
    @11
    cK
    cA
    elfpw
    #
    simprbi
    syl
    #
    wph
    cN
    cC
    cpw
    cfn
    cin
    wcel
    #
    @12
    tsmsxp.n
    @18
    cN
    cC
    wss
    #
    @12
    cN
    cC
    elfpw
    #
    simprbi
    syl
    #
    cK
    cN
    xpfi
    syl2anc
    #
    wph
    cA
    cC
    cxp
    #
    cB
    @0
    cF
    tsmsxp.f
    wph
    @15
    @19
    @0
    @23
    wss
    wph
    @14
    @15
    tsmsxp.k
    @14
    @15
    @11
    @16
    simplbi
    syl
    #
    wph
    @18
    @19
    tsmsxp.n
    @18
    @19
    @12
    @20
    simplbi
    syl
    #
    cK
    cA
    cN
    cC
    xpss12
    syl2anc
    fssresd
    #
    wph
    @0
    cB
    @1
    cL
    c.0
    @26
    @22
    tsmsxp.3
    fdmfifsupp
    #
    gsumcl
    wph
    cK
    cB
    @3
    cG
    cfn
    c.0
    tsmsxp.b
    tsmsxp.z
    tsmsxp.g
    @17
    wph
    cA
    cB
    cK
    cH
    tsmsxp.h
    @24
    fssresd
    #
    wph
    cK
    cB
    @3
    cL
    c.0
    @28
    @17
    tsmsxp.3
    fdmfifsupp
    #
    gsumcl
    cB
    c.pl
    cG
    c.mi
    @2
    @4
    tsmsxp.b
    tsmsxp.p
    tsmsxp.m
    ablpncan3
    syl12anc
    wph
    @2
    cS
    wcel
    @5
    cT
    wcel
    vc
    cv
    #
    vd
    cv
    #
    c.pl
    co
    #
    cU
    wcel
    #
    vd
    cT
    wral
    vc
    cS
    wral
    @6
    cU
    wcel
    #
    tsmsxp.5
    wph
    cG
    vy
    cK
    vy
    cv
    #
    cH
    cfv
    #
    cG
    cF
    @35
    csn
    #
    cN
    cxp
    #
    cres
    #
    cgsu
    co
    #
    c.mi
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @5
    cT
    wph
    cG
    @3
    vy
    cK
    @40
    cmpt
    #
    c.mi
    cof
    co
    #
    cgsu
    co
    @4
    cG
    @44
    cgsu
    co
    #
    c.mi
    co
    @43
    @5
    wph
    cK
    cB
    @3
    cG
    @44
    c.mi
    cfn
    c.0
    tsmsxp.b
    tsmsxp.z
    tsmsxp.m
    @10
    @17
    @28
    wph
    vy
    cK
    @40
    cB
    @44
    wph
    @35
    cK
    wcel
    #
    wa
    #
    @38
    cB
    @39
    cG
    cfn
    c.0
    tsmsxp.b
    tsmsxp.z
    wph
    @9
    @47
    tsmsxp.g
    adantr
    #
    @48
    @37
    cfn
    wcel
    #
    @12
    @38
    cfn
    wcel
    @35
    snfi
    #
    wph
    @12
    @47
    @21
    adantr
    #
    @37
    cN
    xpfi
    sylancr
    #
    @48
    @23
    cB
    @38
    cF
    wph
    @23
    cB
    cF
    wf
    #
    @47
    tsmsxp.f
    adantr
    #
    @48
    @37
    cA
    wss
    @19
    @38
    @23
    wss
    @48
    @35
    cA
    wph
    cK
    cA
    @35
    @24
    sselda
    #
    snssd
    wph
    @19
    @47
    @25
    adantr
    #
    @37
    cA
    cN
    cC
    xpss12
    syl2anc
    fssresd
    #
    @48
    @38
    cB
    @39
    cvv
    c.0
    @58
    @53
    c.0
    cvv
    wcel
    @48
    c.0
    cG
    c0g
    cfv
    cvv
    tsmsxp.z
    cG
    c0g
    fvex
    eqeltri
    a1i
    #
    fdmfifsupp
    #
    gsumcl
    @44
    eqid
    #
    fmptd
    @29
    wph
    vy
    cK
    @44
    cvv
    cL
    @40
    c.0
    @61
    @17
    @48
    cG
    @39
    cgsu
    ovexd
    #
    tsmsxp.3
    fsuppmptdm
    gsumsub
    wph
    @45
    @42
    cG
    cgsu
    wph
    vy
    cK
    @36
    @40
    c.mi
    @3
    @44
    cfn
    cvv
    cvv
    @17
    @48
    @35
    cH
    fvexd
    @62
    wph
    vy
    cA
    cB
    cK
    cH
    tsmsxp.h
    @24
    feqresmpt
    wph
    @44
    eqidd
    offval2
    oveq2d
    wph
    @46
    @2
    @4
    c.mi
    wph
    @46
    cG
    vy
    cK
    cG
    vz
    cN
    @35
    vz
    cv
    #
    @1
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    @2
    wph
    @44
    @67
    cG
    cgsu
    wph
    vy
    cK
    @40
    @66
    @48
    cG
    vw
    @37
    cG
    vz
    cN
    vw
    cv
    #
    @63
    @39
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    cgsu
    co
    #
    cG
    vz
    cN
    @35
    @63
    cF
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @40
    @66
    @48
    cG
    cmnd
    wcel
    #
    @47
    @75
    cB
    wcel
    @72
    @75
    wceq
    @48
    @9
    @76
    @49
    cG
    cmnmnd
    syl
    wph
    @47
    simpr
    @48
    cN
    cB
    @74
    cG
    cfn
    c.0
    tsmsxp.b
    tsmsxp.z
    @49
    @52
    @48
    vz
    cN
    @73
    cB
    @74
    @48
    @63
    cN
    wcel
    #
    wa
    #
    @35
    @63
    cB
    cA
    cC
    cF
    @48
    @54
    @77
    @55
    adantr
    @48
    @35
    cA
    wcel
    @77
    @56
    adantr
    @48
    cN
    cC
    @63
    @57
    sselda
    fovrnd
    @74
    eqid
    #
    fmptd
    @48
    vz
    cN
    @74
    cvv
    cvv
    @73
    c.0
    @79
    @52
    @78
    @35
    @63
    cF
    ovexd
    @59
    fsuppmptdm
    gsumcl
    @71
    cB
    @75
    vw
    cG
    @35
    cK
    tsmsxp.b
    vw
    vy
    weq
    #
    @70
    @74
    cG
    cgsu
    @80
    vz
    cN
    @69
    @73
    @80
    @77
    wa
    @69
    @68
    @63
    cF
    co
    #
    @73
    @80
    @68
    @37
    wcel
    @77
    @69
    @81
    wceq
    vw
    @35
    velsn
    @68
    @63
    @37
    cN
    cF
    ovres
    sylanbr
    @80
    @81
    @73
    wceq
    @77
    @68
    @35
    @63
    cF
    oveq1
    adantr
    eqtrd
    mpteq2dva
    oveq2d
    gsumsn
    syl3anc
    @48
    @37
    cB
    cN
    vw
    vz
    @39
    cG
    cfn
    cfn
    c.0
    tsmsxp.b
    tsmsxp.z
    @49
    @50
    @48
    @51
    a1i
    @52
    @58
    @60
    gsumxp
    @48
    @65
    @74
    cG
    cgsu
    @48
    vz
    cN
    @64
    @73
    @47
    @77
    @64
    @73
    wceq
    wph
    @35
    @63
    cK
    cN
    cF
    ovres
    adantll
    mpteq2dva
    oveq2d
    3eqtr4d
    mpteq2dva
    oveq2d
    wph
    cK
    cB
    cN
    vy
    vz
    @1
    cG
    cfn
    cfn
    c.0
    tsmsxp.b
    tsmsxp.z
    tsmsxp.g
    @17
    @21
    @26
    @27
    gsumxp
    eqtr4d
    oveq2d
    3eqtr3d
    wph
    @42
    cL
    cK
    cmap
    co
    #
    wcel
    #
    cG
    vg
    cv
    #
    cgsu
    co
    #
    cT
    wcel
    #
    vg
    @82
    wral
    @43
    cT
    wcel
    #
    wph
    @83
    cK
    cL
    @42
    wf
    wph
    vy
    cK
    @41
    cL
    @42
    wph
    vx
    cv
    #
    cH
    cfv
    #
    cG
    cF
    @88
    csn
    #
    cN
    cxp
    #
    cres
    #
    cgsu
    co
    #
    c.mi
    co
    #
    cL
    wcel
    #
    vx
    cK
    wral
    @47
    @41
    cL
    wcel
    #
    tsmsxp.x
    @95
    @96
    vx
    @35
    cK
    vx
    vy
    weq
    #
    @94
    @41
    cL
    @97
    @89
    @36
    @93
    @40
    c.mi
    @88
    @35
    cH
    fveq2
    @97
    @92
    @39
    cG
    cgsu
    @97
    @91
    @38
    cF
    @97
    @90
    @37
    cN
    @88
    @35
    sneq
    xpeq1d
    reseq2d
    oveq2d
    oveq12d
    eleq1d
    rspccva
    sylan
    @42
    eqid
    fmptd
    wph
    cL
    cK
    @42
    cJ
    @13
    tsmsxp.l
    tsmsxp.k
    elmapd
    mpbird
    tsmsxp.6
    @86
    @87
    vg
    @42
    @82
    @84
    @42
    wceq
    @85
    @43
    cT
    @84
    @42
    cG
    cgsu
    oveq2
    eleq1d
    rspcv
    sylc
    eqeltrrd
    tsmsxp.4
    @33
    @34
    @2
    @31
    c.pl
    co
    #
    cU
    wcel
    vc
    vd
    @2
    @5
    cS
    cT
    @30
    @2
    wceq
    @32
    @98
    cU
    @30
    @2
    @31
    c.pl
    oveq1
    eleq1d
    @31
    @5
    wceq
    @98
    @6
    cU
    @31
    @5
    @2
    c.pl
    oveq2
    eleq1d
    rspc2va
    syl21anc
    eqeltrrd
end
