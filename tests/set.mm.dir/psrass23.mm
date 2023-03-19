include "co.mm"
include "wceq.mm"
include "psrass23l.mm"
include "cv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "crab.mm"
include "cfv.mm"
include "cmin.mm"
include "cof.mm"
include "cmulr.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "eqid.mm"
include "adantr.mm"
include "syl6eleq.mm"
include "ad2antrr.mm"
include "ssrab2.mm"
include "simplr.mm"
include "simpr.mm"
include "psrbagconcl.mm"
include "syl3anc.mm"
include "sseldi.mm"
include "psrvscaval.mm"
include "oveq2d.mm"
include "psrelbas.mm"
include "ffvelrnd.mm"
include "ccrg.mm"
include "crngcom.mm"
include "3expb.mm"
include "sylan.mm"
include "crg.mm"
include "w3a.mm"
include "ringass.mm"
include "caov12d.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "cplusg.mm"
include "cfn.mm"
include "c0g.mm"
include "psrbaglefi.mm"
include "ringcl.mm"
include "cvv.mm"
include "wfun.mm"
include "csupp.mm"
include "wss.mm"
include "cfsupp.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cn0.mm"
include "cmap.mm"
include "ovex.mm"
include "rabex2.mm"
include "mptrabex.mm"
include "funmpt.mm"
include "fvex.mm"
include "3pm3.2i.mm"
include "a1i.mm"
include "cdm.mm"
include "suppssdm.mm"
include "dmmptss.mm"
include "sstri.mm"
include "suppssfifsupp.mm"
include "syl12anc.mm"
include "gsummulc2.mm"
include "psrvscacl.mm"
include "psrmulfval.mm"
include "csn.mm"
include "cxp.mm"
include "psrmulcl.mm"
include "psrvsca.mm"
include "fconstmpt.mm"
include "offval2.mm"
include "3eqtr4d.mm"
include "jca.mm"

theorem psrass23
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let vf: setvar f
  let cI: class I
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  let c.pl: class .+
  let vy: setvar y
  let vz: setvar z
  let c.0: class .0.
  let vg: setvar g
  let vh: setvar h
  let vj: setvar j
  let vn: setvar n
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vu: setvar u
  let vv: setvar v
  let cU: class U
  let cZ: class Z
  let c.1: class .1.
  assume psrring.s: |- S = ( I mPwSer R )
  assume psrring.i: |- ( ph -> I e. V )
  assume psrring.r: |- ( ph -> R e. Ring )
  assume psrass.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume psrass.t: |- .X. = ( .r ` S )
  assume psrass.b: |- B = ( Base ` S )
  assume psrass.x: |- ( ph -> X e. B )
  assume psrass.y: |- ( ph -> Y e. B )
  assume psrcom.c: |- ( ph -> R e. CRing )
  assume psrass.k: |- K = ( Base ` R )
  assume psrass.n: |- .x. = ( .s ` S )
  assume psrass.a: |- ( ph -> A e. K )

  disjoint I f
  disjoint R f
  disjoint X f
  disjoint Y f
  disjoint k x
  disjoint .+ k
  disjoint .+ x
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint .0. f
  disjoint x y
  disjoint x z
  disjoint .0. x
  disjoint y z
  disjoint .0. y
  disjoint .0. z
  disjoint f g
  disjoint f h
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f w
  disjoint g h
  disjoint g j
  disjoint g k
  disjoint g n
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint I g
  disjoint h j
  disjoint h k
  disjoint h n
  disjoint h r
  disjoint h s
  disjoint h t
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint I h
  disjoint j k
  disjoint j n
  disjoint j r
  disjoint j s
  disjoint j t
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint I j
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint k t
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint I k
  disjoint n r
  disjoint n s
  disjoint n t
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint I n
  disjoint r s
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint I r
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint I s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint I t
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint K k
  disjoint k u
  disjoint k v
  disjoint A k
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint B j
  disjoint B k
  disjoint B n
  disjoint B x
  disjoint B z
  disjoint f u
  disjoint f v
  disjoint g u
  disjoint g v
  disjoint R g
  disjoint h u
  disjoint h v
  disjoint R h
  disjoint j u
  disjoint j v
  disjoint R j
  disjoint R k
  disjoint n u
  disjoint n v
  disjoint R n
  disjoint r u
  disjoint r v
  disjoint R r
  disjoint s u
  disjoint s v
  disjoint R s
  disjoint t u
  disjoint t v
  disjoint R t
  disjoint u y
  disjoint u z
  disjoint R u
  disjoint v y
  disjoint v z
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint D g
  disjoint D h
  disjoint D j
  disjoint D k
  disjoint D n
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint U y
  disjoint U z
  disjoint X g
  disjoint X h
  disjoint X j
  disjoint X k
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint V g
  disjoint V h
  disjoint V j
  disjoint V k
  disjoint V r
  disjoint V w
  disjoint V x
  disjoint V y
  disjoint .x. k
  disjoint .x. x
  disjoint .x. y
  disjoint Z f
  disjoint Z g
  disjoint Z h
  disjoint Z j
  disjoint Z k
  disjoint Z n
  disjoint Z x
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint .1. x
  disjoint .1. y
  disjoint .X. j
  disjoint .X. k
  disjoint .X. x
  disjoint Y g
  disjoint Y h
  disjoint Y j
  disjoint Y k
  disjoint Y n
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  assert |- ( ph -> ( ( ( A .x. X ) .X. Y ) = ( A .x. ( X .X. Y ) ) /\ ( X .X. ( A .x. Y ) ) = ( A .x. ( X .X. Y ) ) ) )

  proof
    wph
    cA
    cX
    c.x
    co
    cY
    c.xp
    co
    cA
    cX
    cY
    c.xp
    co
    #
    c.x
    co
    #
    wceq
    cX
    cA
    cY
    c.x
    co
    #
    c.xp
    co
    #
    @1
    wceq
    wph
    cA
    cB
    cD
    cR
    cS
    c.x
    c.xp
    vf
    cI
    cK
    cV
    cX
    cY
    psrring.s
    psrring.i
    psrring.r
    psrass.d
    psrass.t
    psrass.b
    psrass.x
    psrass.y
    psrass.k
    psrass.n
    psrass.a
    psrass23l
    wph
    vk
    cD
    cR
    vx
    vy
    cv
    vk
    cv
    #
    cle
    cofr
    wbr
    #
    vy
    cD
    crab
    #
    vx
    cv
    #
    cX
    cfv
    #
    @4
    @7
    cmin
    cof
    co
    #
    @2
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    vk
    cD
    cA
    cR
    vx
    @6
    @8
    @9
    cY
    cfv
    #
    @11
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @11
    co
    #
    cmpt
    #
    @3
    @1
    wph
    vk
    cD
    @14
    @19
    wph
    @4
    cD
    wcel
    #
    wa
    #
    @14
    cR
    vx
    @6
    cA
    @16
    @11
    co
    #
    cmpt
    #
    cgsu
    co
    @19
    @22
    @13
    @24
    cR
    cgsu
    @22
    vx
    @6
    @12
    @23
    @22
    @7
    @6
    wcel
    #
    wa
    #
    @12
    @8
    cA
    @15
    @11
    co
    #
    @11
    co
    @23
    @26
    @10
    @27
    @8
    @11
    @26
    cB
    cD
    cR
    cS
    c.x
    @11
    vf
    cY
    cI
    cR
    cbs
    cfv
    #
    cA
    @9
    psrring.s
    psrass.n
    @28
    eqid
    #
    psrass.b
    @11
    eqid
    #
    psrass.d
    @22
    cA
    @28
    wcel
    @25
    @22
    cA
    cK
    @28
    wph
    cA
    cK
    wcel
    @21
    psrass.a
    adantr
    #
    psrass.k
    syl6eleq
    #
    adantr
    #
    wph
    cY
    cB
    wcel
    @21
    @25
    psrass.y
    ad2antrr
    #
    @26
    @6
    cD
    @9
    @5
    vy
    cD
    ssrab2
    #
    @26
    cI
    cV
    wcel
    #
    @21
    @25
    @9
    @6
    wcel
    wph
    @36
    @21
    @25
    psrring.i
    ad2antrr
    wph
    @21
    @25
    simplr
    @22
    @25
    simpr
    #
    vy
    cD
    @6
    vf
    @4
    cI
    cV
    @7
    psrass.d
    @6
    eqid
    psrbagconcl
    syl3anc
    sseldi
    #
    psrvscaval
    oveq2d
    @26
    vu
    vv
    vw
    @8
    cA
    @15
    @28
    @11
    @26
    cD
    @28
    @7
    cX
    @26
    cB
    cD
    cR
    cS
    vf
    cI
    @28
    cX
    psrring.s
    @29
    psrass.d
    psrass.b
    wph
    cX
    cB
    wcel
    @21
    @25
    psrass.x
    ad2antrr
    psrelbas
    @26
    @6
    cD
    @7
    @35
    @37
    sseldi
    ffvelrnd
    #
    @33
    @26
    cD
    @28
    @9
    cY
    @26
    cB
    cD
    cR
    cS
    vf
    cI
    @28
    cY
    psrring.s
    @29
    psrass.d
    psrass.b
    @34
    psrelbas
    @38
    ffvelrnd
    #
    @26
    cR
    ccrg
    wcel
    #
    vu
    cv
    #
    @28
    wcel
    #
    vv
    cv
    #
    @28
    wcel
    #
    wa
    @42
    @44
    @11
    co
    #
    @44
    @42
    @11
    co
    wceq
    #
    wph
    @41
    @21
    @25
    psrcom.c
    ad2antrr
    @41
    @43
    @45
    @47
    @28
    cR
    @11
    @42
    @44
    @29
    @30
    crngcom
    3expb
    sylan
    @26
    cR
    crg
    wcel
    #
    @43
    @45
    vw
    cv
    #
    @28
    wcel
    w3a
    @46
    @49
    @11
    co
    @42
    @44
    @49
    @11
    co
    @11
    co
    wceq
    wph
    @48
    @21
    @25
    psrring.r
    ad2antrr
    #
    @28
    cR
    @11
    @42
    @44
    @49
    @29
    @30
    ringass
    sylan
    caov12d
    eqtrd
    mpteq2dva
    oveq2d
    @22
    @6
    @28
    cR
    cplusg
    cfv
    #
    cR
    @11
    vx
    cfn
    @16
    cA
    cR
    c0g
    cfv
    #
    @29
    @52
    eqid
    @51
    eqid
    @30
    wph
    @48
    @21
    psrring.r
    adantr
    wph
    @36
    @21
    @6
    cfn
    wcel
    #
    psrring.i
    vy
    cD
    vf
    @4
    cI
    cV
    psrass.d
    psrbaglefi
    sylan
    #
    @32
    @26
    @48
    @8
    @28
    wcel
    @15
    @28
    wcel
    @16
    @28
    wcel
    @50
    @39
    @40
    @28
    cR
    @11
    @8
    @15
    @29
    @30
    ringcl
    syl3anc
    @22
    @17
    cvv
    wcel
    #
    @17
    wfun
    #
    @52
    cvv
    wcel
    #
    w3a
    #
    @53
    @17
    @52
    csupp
    co
    #
    @6
    wss
    #
    @17
    @52
    cfsupp
    wbr
    @58
    @22
    @55
    @56
    @57
    @5
    vx
    vy
    cD
    @16
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    cI
    cmap
    co
    cD
    psrass.d
    cn0
    cI
    cmap
    ovex
    rabex2
    #
    mptrabex
    vx
    @6
    @16
    funmpt
    cR
    c0g
    fvex
    3pm3.2i
    a1i
    @54
    @60
    @22
    @59
    @17
    cdm
    @6
    @17
    @52
    suppssdm
    vx
    @6
    @16
    @17
    @17
    eqid
    dmmptss
    sstri
    a1i
    @6
    @17
    cvv
    cvv
    @52
    suppssfifsupp
    syl12anc
    gsummulc2
    eqtrd
    mpteq2dva
    wph
    vx
    vy
    cB
    cD
    cR
    cS
    c.xp
    @11
    vf
    vk
    cX
    @2
    cI
    psrring.s
    psrass.b
    @30
    psrass.t
    psrass.d
    psrass.x
    wph
    cB
    cR
    cS
    c.x
    cY
    cI
    cK
    cA
    psrring.s
    psrass.n
    psrass.k
    psrass.b
    psrring.r
    psrass.a
    psrass.y
    psrvscacl
    psrmulfval
    wph
    @1
    cD
    cA
    csn
    cxp
    #
    @0
    @11
    cof
    co
    @20
    wph
    cB
    cD
    cR
    cS
    c.x
    @11
    vf
    @0
    cI
    cK
    cA
    psrring.s
    psrass.n
    psrass.k
    psrass.b
    @30
    psrass.d
    psrass.a
    wph
    cB
    cR
    cS
    c.xp
    cI
    cX
    cY
    psrring.s
    psrass.b
    psrass.t
    psrring.r
    psrass.x
    psrass.y
    psrmulcl
    psrvsca
    wph
    vk
    cD
    cA
    @18
    @11
    @62
    @0
    cvv
    cK
    cvv
    cD
    cvv
    wcel
    wph
    @61
    a1i
    @31
    @18
    cvv
    wcel
    @22
    cR
    @17
    cgsu
    ovex
    a1i
    @62
    vk
    cD
    cA
    cmpt
    wceq
    wph
    vk
    cD
    cA
    fconstmpt
    a1i
    wph
    vx
    vy
    cB
    cD
    cR
    cS
    c.xp
    @11
    vf
    vk
    cX
    cY
    cI
    psrring.s
    psrass.b
    @30
    psrass.t
    psrass.d
    psrass.x
    psrass.y
    psrmulfval
    offval2
    eqtrd
    3eqtr4d
    jca
end
