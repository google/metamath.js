include "cv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "crab.mm"
include "co.mm"
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
include "simpr.mm"
include "sseldi.mm"
include "psrvscaval.mm"
include "oveq1d.mm"
include "crg.mm"
include "wceq.mm"
include "psrelbas.mm"
include "ffvelrnd.mm"
include "simplr.mm"
include "psrbagconcl.mm"
include "syl3anc.mm"
include "ringass.mm"
include "syl13anc.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "cplusg.mm"
include "cfn.mm"
include "c0g.mm"
include "psrbaglefi.mm"
include "sylan.mm"
include "ringcl.mm"
include "cvv.mm"
include "wfun.mm"
include "w3a.mm"
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
include "ovexd.mm"
include "fconstmpt.mm"
include "offval2.mm"
include "3eqtr4d.mm"

theorem psrass23l
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
  assume psrass23l.k: |- K = ( Base ` R )
  assume psrass23l.n: |- .x. = ( .s ` S )
  assume psrass23l.a: |- ( ph -> A e. K )

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
  assert |- ( ph -> ( ( A .x. X ) .X. Y ) = ( A .x. ( X .X. Y ) ) )

  proof
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
    cA
    cX
    c.x
    co
    #
    cfv
    #
    @0
    @3
    cmin
    cof
    co
    #
    cY
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
    @2
    @3
    cX
    cfv
    #
    @7
    @8
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @8
    co
    #
    cmpt
    #
    @4
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
    wph
    vk
    cD
    @11
    @16
    wph
    @0
    cD
    wcel
    #
    wa
    #
    @11
    cR
    vx
    @2
    cA
    @13
    @8
    co
    #
    cmpt
    #
    cgsu
    co
    @16
    @21
    @10
    @23
    cR
    cgsu
    @21
    vx
    @2
    @9
    @22
    @21
    @3
    @2
    wcel
    #
    wa
    #
    @9
    cA
    @12
    @8
    co
    #
    @7
    @8
    co
    #
    @22
    @25
    @5
    @26
    @7
    @8
    @25
    cB
    cD
    cR
    cS
    c.x
    @8
    vf
    cX
    cI
    cR
    cbs
    cfv
    #
    cA
    @3
    psrring.s
    psrass23l.n
    @28
    eqid
    #
    psrass.b
    @8
    eqid
    #
    psrass.d
    @21
    cA
    @28
    wcel
    #
    @24
    @21
    cA
    cK
    @28
    wph
    cA
    cK
    wcel
    @20
    psrass23l.a
    adantr
    #
    psrass23l.k
    syl6eleq
    #
    adantr
    #
    wph
    cX
    cB
    wcel
    @20
    @24
    psrass.x
    ad2antrr
    #
    @25
    @2
    cD
    @3
    @1
    vy
    cD
    ssrab2
    #
    @21
    @24
    simpr
    #
    sseldi
    #
    psrvscaval
    oveq1d
    @25
    cR
    crg
    wcel
    #
    @31
    @12
    @28
    wcel
    #
    @7
    @28
    wcel
    #
    @27
    @22
    wceq
    wph
    @39
    @20
    @24
    psrring.r
    ad2antrr
    #
    @34
    @25
    cD
    @28
    @3
    cX
    @25
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
    @35
    psrelbas
    @38
    ffvelrnd
    #
    @25
    cD
    @28
    @6
    cY
    @25
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
    wph
    cY
    cB
    wcel
    @20
    @24
    psrass.y
    ad2antrr
    psrelbas
    @25
    @2
    cD
    @6
    @36
    @25
    cI
    cV
    wcel
    #
    @20
    @24
    @6
    @2
    wcel
    wph
    @44
    @20
    @24
    psrring.i
    ad2antrr
    wph
    @20
    @24
    simplr
    @37
    vy
    cD
    @2
    vf
    @0
    cI
    cV
    @3
    psrass.d
    @2
    eqid
    psrbagconcl
    syl3anc
    sseldi
    ffvelrnd
    #
    @28
    cR
    @8
    cA
    @12
    @7
    @29
    @30
    ringass
    syl13anc
    eqtrd
    mpteq2dva
    oveq2d
    @21
    @2
    @28
    cR
    cplusg
    cfv
    #
    cR
    @8
    vx
    cfn
    @13
    cA
    cR
    c0g
    cfv
    #
    @29
    @47
    eqid
    @46
    eqid
    @30
    wph
    @39
    @20
    psrring.r
    adantr
    wph
    @44
    @20
    @2
    cfn
    wcel
    #
    psrring.i
    vy
    cD
    vf
    @0
    cI
    cV
    psrass.d
    psrbaglefi
    sylan
    #
    @33
    @25
    @39
    @40
    @41
    @13
    @28
    wcel
    @42
    @43
    @45
    @28
    cR
    @8
    @12
    @7
    @29
    @30
    ringcl
    syl3anc
    @21
    @14
    cvv
    wcel
    #
    @14
    wfun
    #
    @47
    cvv
    wcel
    #
    w3a
    #
    @48
    @14
    @47
    csupp
    co
    #
    @2
    wss
    #
    @14
    @47
    cfsupp
    wbr
    @53
    @21
    @50
    @51
    @52
    @1
    vx
    vy
    cD
    @13
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
    @2
    @13
    funmpt
    cR
    c0g
    fvex
    3pm3.2i
    a1i
    @49
    @55
    @21
    @54
    @14
    cdm
    @2
    @14
    @47
    suppssdm
    vx
    @2
    @13
    @14
    @14
    eqid
    dmmptss
    sstri
    a1i
    @2
    @14
    cvv
    cvv
    @47
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
    @8
    vf
    vk
    @4
    cY
    cI
    psrring.s
    psrass.b
    @30
    psrass.t
    psrass.d
    wph
    cB
    cR
    cS
    c.x
    cX
    cI
    cK
    cA
    psrring.s
    psrass23l.n
    psrass23l.k
    psrass.b
    psrring.r
    psrass23l.a
    psrass.x
    psrvscacl
    psrass.y
    psrmulfval
    wph
    @19
    cD
    cA
    csn
    cxp
    #
    @18
    @8
    cof
    co
    @17
    wph
    cB
    cD
    cR
    cS
    c.x
    @8
    vf
    @18
    cI
    cK
    cA
    psrring.s
    psrass23l.n
    psrass23l.k
    psrass.b
    @30
    psrass.d
    psrass23l.a
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
    @15
    @8
    @57
    @18
    cvv
    cK
    cvv
    cD
    cvv
    wcel
    wph
    @56
    a1i
    @32
    @21
    cR
    @14
    cgsu
    ovexd
    @57
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
    @8
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
end
