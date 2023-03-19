include "cv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "crab.mm"
include "cfv.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cmulr.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wcel.mm"
include "wa.mm"
include "ccom.mm"
include "cbs.mm"
include "cfn.mm"
include "c0g.mm"
include "eqid.mm"
include "ccmn.mm"
include "crg.mm"
include "ringcmn.mm"
include "syl.mm"
include "adantr.mm"
include "psrbaglefi.mm"
include "sylan.mm"
include "ad2antrr.mm"
include "wf.mm"
include "psrelbas.mm"
include "simpr.mm"
include "breq1.mm"
include "elrab.mm"
include "sylib.mm"
include "simpld.mm"
include "ffvelrnd.mm"
include "cn0.mm"
include "simplr.mm"
include "psrbagf.mm"
include "syl2anc.mm"
include "simprd.mm"
include "psrbagcon.mm"
include "syl13anc.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "fmptd.mm"
include "cvv.mm"
include "wfun.mm"
include "csupp.mm"
include "wss.mm"
include "cfsupp.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cmap.mm"
include "ovex.mm"
include "rabex2.mm"
include "a1i.mm"
include "rabexg.mm"
include "mptexg.mm"
include "funmpt.mm"
include "fvexd.mm"
include "cdm.mm"
include "suppssdm.mm"
include "dmmptss.mm"
include "sstri.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"
include "wf1o.mm"
include "psrbagconf1o.mm"
include "gsumf1o.mm"
include "psrbagconcl.mm"
include "eqidd.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "fmptco.mm"
include "ffvelrnda.mm"
include "cc.mm"
include "nn0cn.mm"
include "nncan.mm"
include "syl2an.mm"
include "mpteq2dva.mm"
include "feqmptd.mm"
include "offval2.mm"
include "3eqtr4d.mm"
include "oveq2d.mm"
include "ccrg.mm"
include "crngcom.mm"
include "eqtrd.mm"
include "psrmulfval.mm"

theorem psrcom
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let c.xp: class .X.
  let vf: setvar f
  let cI: class I
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
  let cK: class K
  let vu: setvar u
  let vv: setvar v
  let cA: class A
  let cU: class U
  let c.x: class .x.
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
  assert |- ( ph -> ( X .X. Y ) = ( Y .X. X ) )

  proof
    wph
    vx
    cD
    cR
    vk
    vg
    cv
    #
    vx
    cv
    #
    cle
    cofr
    #
    wbr
    #
    vg
    cD
    crab
    #
    vk
    cv
    #
    cX
    cfv
    #
    @1
    @5
    cmin
    cof
    #
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
    vx
    cD
    cR
    vj
    @4
    vj
    cv
    #
    cY
    cfv
    #
    @1
    @14
    @7
    co
    #
    cX
    cfv
    #
    @10
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    cX
    cY
    c.xp
    co
    cY
    cX
    c.xp
    co
    wph
    vx
    cD
    @13
    @20
    wph
    @1
    cD
    wcel
    #
    wa
    #
    @13
    cR
    @12
    vj
    @4
    @16
    cmpt
    #
    ccom
    #
    cgsu
    co
    @20
    @22
    @4
    cR
    cbs
    cfv
    #
    @4
    @12
    cR
    @23
    cfn
    cR
    c0g
    cfv
    #
    @25
    eqid
    #
    @26
    eqid
    wph
    cR
    ccmn
    wcel
    #
    @21
    wph
    cR
    crg
    wcel
    #
    @28
    psrring.r
    cR
    ringcmn
    syl
    adantr
    wph
    cI
    cV
    wcel
    #
    @21
    @4
    cfn
    wcel
    #
    psrring.i
    vg
    cD
    vf
    @1
    cI
    cV
    psrass.d
    psrbaglefi
    sylan
    #
    @22
    vk
    @4
    @11
    @25
    @12
    @22
    @5
    @4
    wcel
    #
    wa
    #
    @29
    @6
    @25
    wcel
    @9
    @25
    wcel
    @11
    @25
    wcel
    wph
    @29
    @21
    @33
    psrring.r
    ad2antrr
    @34
    cD
    @25
    @5
    cX
    wph
    cD
    @25
    cX
    wf
    #
    @21
    @33
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @25
    cX
    psrring.s
    @27
    psrass.d
    psrass.b
    psrass.x
    psrelbas
    #
    ad2antrr
    @34
    @5
    cD
    wcel
    #
    @5
    @1
    @2
    wbr
    #
    @34
    @33
    @37
    @38
    wa
    @22
    @33
    simpr
    @3
    @38
    vg
    @5
    cD
    @0
    @5
    @1
    @2
    breq1
    elrab
    sylib
    #
    simpld
    #
    ffvelrnd
    @34
    cD
    @25
    @8
    cY
    wph
    cD
    @25
    cY
    wf
    #
    @21
    @33
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @25
    cY
    psrring.s
    @27
    psrass.d
    psrass.b
    psrass.y
    psrelbas
    #
    ad2antrr
    @34
    @8
    cD
    wcel
    #
    @8
    @1
    @2
    wbr
    #
    @34
    @30
    @21
    cI
    cn0
    @5
    wf
    #
    @38
    @43
    @44
    wa
    wph
    @30
    @21
    @33
    psrring.i
    ad2antrr
    #
    wph
    @21
    @33
    simplr
    @34
    @30
    @37
    @45
    @46
    @40
    cD
    vf
    @5
    cI
    cV
    psrass.d
    psrbagf
    syl2anc
    @34
    @37
    @38
    @39
    simprd
    cD
    vf
    @1
    @5
    cI
    cV
    psrass.d
    psrbagcon
    syl13anc
    simpld
    ffvelrnd
    @25
    cR
    @10
    @6
    @9
    @27
    @10
    eqid
    #
    ringcl
    syl3anc
    @12
    eqid
    #
    fmptd
    @22
    @12
    cvv
    wcel
    #
    @12
    wfun
    #
    @26
    cvv
    wcel
    @31
    @12
    @26
    csupp
    co
    #
    @4
    wss
    #
    @12
    @26
    cfsupp
    wbr
    @22
    @4
    cvv
    wcel
    #
    @49
    @22
    cD
    cvv
    wcel
    #
    @53
    @54
    @22
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
    a1i
    @3
    vg
    cD
    cvv
    rabexg
    syl
    vk
    @4
    @11
    cvv
    mptexg
    syl
    @50
    @22
    vk
    @4
    @11
    funmpt
    a1i
    @22
    cR
    c0g
    fvexd
    @32
    @52
    @22
    @51
    @12
    cdm
    @4
    @12
    @26
    suppssdm
    vk
    @4
    @11
    @12
    @48
    dmmptss
    sstri
    a1i
    @4
    @12
    cvv
    cvv
    @26
    suppssfifsupp
    syl32anc
    wph
    @30
    @21
    @4
    @4
    @23
    wf1o
    psrring.i
    vj
    vg
    cD
    @4
    vf
    @1
    cI
    cV
    psrass.d
    @4
    eqid
    #
    psrbagconf1o
    sylan
    gsumf1o
    @22
    @24
    @19
    cR
    cgsu
    @22
    @24
    vj
    @4
    @17
    @1
    @16
    @7
    co
    #
    cY
    cfv
    #
    @10
    co
    #
    cmpt
    @19
    @22
    vj
    vk
    @4
    @4
    @16
    @11
    @58
    @23
    @12
    @22
    @14
    @4
    wcel
    #
    wa
    #
    @30
    @21
    @59
    @16
    @4
    wcel
    wph
    @30
    @21
    @59
    psrring.i
    ad2antrr
    #
    wph
    @21
    @59
    simplr
    #
    @22
    @59
    simpr
    #
    vg
    cD
    @4
    vf
    @1
    cI
    cV
    @14
    psrass.d
    @55
    psrbagconcl
    syl3anc
    @22
    @23
    eqidd
    @22
    @12
    eqidd
    @5
    @16
    wceq
    #
    @6
    @17
    @9
    @57
    @10
    @5
    @16
    cX
    fveq2
    @64
    @8
    @56
    cY
    @5
    @16
    @1
    @7
    oveq2
    fveq2d
    oveq12d
    fmptco
    @22
    vj
    @4
    @58
    @18
    @60
    @58
    @17
    @15
    @10
    co
    #
    @18
    @60
    @57
    @15
    @17
    @10
    @60
    @56
    @14
    cY
    @60
    vz
    cI
    vz
    cv
    #
    @1
    cfv
    #
    @67
    @66
    @14
    cfv
    #
    cmin
    co
    #
    cmin
    co
    #
    cmpt
    vz
    cI
    @68
    cmpt
    @56
    @14
    @60
    vz
    cI
    @70
    @68
    @60
    @66
    cI
    wcel
    wa
    #
    @67
    cn0
    wcel
    #
    @68
    cn0
    wcel
    #
    @70
    @68
    wceq
    #
    @60
    cI
    cn0
    @66
    @1
    @22
    cI
    cn0
    @1
    wf
    #
    @59
    wph
    @30
    @21
    @75
    psrring.i
    cD
    vf
    @1
    cI
    cV
    psrass.d
    psrbagf
    sylan
    adantr
    #
    ffvelrnda
    #
    @60
    cI
    cn0
    @66
    @14
    @60
    @30
    @14
    cD
    wcel
    #
    cI
    cn0
    @14
    wf
    #
    @61
    @60
    @78
    @14
    @1
    @2
    wbr
    #
    @60
    @59
    @78
    @80
    wa
    @63
    @3
    @80
    vg
    @14
    cD
    @0
    @14
    @1
    @2
    breq1
    elrab
    sylib
    #
    simpld
    #
    cD
    vf
    @14
    cI
    cV
    psrass.d
    psrbagf
    syl2anc
    #
    ffvelrnda
    #
    @72
    @67
    cc
    wcel
    @68
    cc
    wcel
    @74
    @73
    @67
    nn0cn
    @68
    nn0cn
    @67
    @68
    nncan
    syl2an
    syl2anc
    mpteq2dva
    @60
    vz
    cI
    @67
    @69
    cmin
    @1
    @16
    cV
    cn0
    cvv
    @61
    @77
    @69
    cvv
    wcel
    @71
    @67
    @68
    cmin
    ovex
    a1i
    @60
    vz
    cI
    cn0
    @1
    @76
    feqmptd
    #
    @60
    vz
    cI
    @67
    @68
    cmin
    @1
    @14
    cV
    cn0
    cn0
    @61
    @77
    @84
    @85
    @60
    vz
    cI
    cn0
    @14
    @83
    feqmptd
    #
    offval2
    offval2
    @86
    3eqtr4d
    fveq2d
    oveq2d
    @60
    cR
    ccrg
    wcel
    #
    @17
    @25
    wcel
    @15
    @25
    wcel
    @65
    @18
    wceq
    wph
    @87
    @21
    @59
    psrcom.c
    ad2antrr
    @60
    cD
    @25
    @16
    cX
    wph
    @35
    @21
    @59
    @36
    ad2antrr
    @60
    @16
    cD
    wcel
    #
    @16
    @1
    @2
    wbr
    #
    @60
    @30
    @21
    @79
    @80
    @88
    @89
    wa
    @61
    @62
    @83
    @60
    @78
    @80
    @81
    simprd
    cD
    vf
    @1
    @14
    cI
    cV
    psrass.d
    psrbagcon
    syl13anc
    simpld
    ffvelrnd
    @60
    cD
    @25
    @14
    cY
    wph
    @41
    @21
    @59
    @42
    ad2antrr
    @82
    ffvelrnd
    @25
    cR
    @10
    @17
    @15
    @27
    @47
    crngcom
    syl3anc
    eqtrd
    mpteq2dva
    eqtrd
    oveq2d
    eqtrd
    mpteq2dva
    wph
    vk
    vg
    cB
    cD
    cR
    cS
    c.xp
    @10
    vf
    vx
    cX
    cY
    cI
    psrring.s
    psrass.b
    @47
    psrass.t
    psrass.d
    psrass.x
    psrass.y
    psrmulfval
    wph
    vj
    vg
    cB
    cD
    cR
    cS
    c.xp
    @10
    vf
    vx
    cY
    cX
    cI
    psrring.s
    psrass.b
    @47
    psrass.t
    psrass.d
    psrass.y
    psrass.x
    psrmulfval
    3eqtr4d
end
