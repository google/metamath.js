include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "psrmulcl.mm"
include "psrelbas.mm"
include "ffnd.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "crab.mm"
include "cmin.mm"
include "cof.mm"
include "cmulr.mm"
include "cmpt.mm"
include "cgsu.mm"
include "adantr.mm"
include "simpr.mm"
include "ccmn.mm"
include "crg.mm"
include "ringcmn.mm"
include "syl.mm"
include "ad2antrr.mm"
include "wf.mm"
include "breq1.mm"
include "elrab.mm"
include "sylib.mm"
include "simpld.mm"
include "ffvelrnd.mm"
include "ad3antrrr.mm"
include "cn0.mm"
include "simplr.mm"
include "psrbagf.mm"
include "syl2anc.mm"
include "simprd.mm"
include "psrbagcon.mm"
include "syl13anc.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "anasss.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "oveq2d.mm"
include "psrass1lem.mm"
include "psrmulval.mm"
include "oveq1d.mm"
include "cplusg.mm"
include "cfn.mm"
include "c0g.mm"
include "psrbaglefi.mm"
include "cvv.mm"
include "fvex.mm"
include "a1i.mm"
include "fsuppmptdm.mm"
include "gsummulc1.mm"
include "ringass.mm"
include "sylan.mm"
include "ffvelrnda.mm"
include "cc.mm"
include "nn0cn.mm"
include "nnncan2.mm"
include "syl3an.mm"
include "mpteq2dva.mm"
include "ovexd.mm"
include "feqmptd.mm"
include "offval2.mm"
include "3eqtr4d.mm"
include "eqtr4d.mm"
include "3eqtr2d.mm"
include "wfun.mm"
include "w3a.mm"
include "csupp.mm"
include "wss.mm"
include "cfsupp.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cmap.mm"
include "ovex.mm"
include "rab2ex.mm"
include "mptex.mm"
include "funmpt.mm"
include "3pm3.2i.mm"
include "cdm.mm"
include "suppssdm.mm"
include "dmmptss.mm"
include "sstri.mm"
include "suppssfifsupp.mm"
include "syl12anc.mm"
include "gsummulc2.mm"
include "eqfnfvd.mm"

theorem psrass1
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
  let cZ: class Z
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
  let c.1: class .1.
  assume psrring.s: |- S = ( I mPwSer R )
  assume psrring.i: |- ( ph -> I e. V )
  assume psrring.r: |- ( ph -> R e. Ring )
  assume psrass.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume psrass.t: |- .X. = ( .r ` S )
  assume psrass.b: |- B = ( Base ` S )
  assume psrass.x: |- ( ph -> X e. B )
  assume psrass.y: |- ( ph -> Y e. B )
  assume psrass.z: |- ( ph -> Z e. B )

  disjoint I f
  disjoint R f
  disjoint X f
  disjoint Z f
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
  assert |- ( ph -> ( ( X .X. Y ) .X. Z ) = ( X .X. ( Y .X. Z ) ) )

  proof
    wph
    vx
    cD
    cX
    cY
    c.xp
    co
    #
    cZ
    c.xp
    co
    #
    cX
    cY
    cZ
    c.xp
    co
    #
    c.xp
    co
    #
    wph
    cD
    cR
    cbs
    cfv
    #
    @1
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @4
    @1
    psrring.s
    @4
    eqid
    #
    psrass.d
    psrass.b
    wph
    cB
    cR
    cS
    c.xp
    cI
    @0
    cZ
    psrring.s
    psrass.b
    psrass.t
    psrring.r
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
    #
    psrass.z
    psrmulcl
    psrelbas
    ffnd
    wph
    cD
    @4
    @3
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @4
    @3
    psrring.s
    @5
    psrass.d
    psrass.b
    wph
    cB
    cR
    cS
    c.xp
    cI
    cX
    @2
    psrring.s
    psrass.b
    psrass.t
    psrring.r
    psrass.x
    wph
    cB
    cR
    cS
    c.xp
    cI
    cY
    cZ
    psrring.s
    psrass.b
    psrass.t
    psrring.r
    psrass.y
    psrass.z
    psrmulcl
    #
    psrmulcl
    psrelbas
    ffnd
    wph
    vx
    cv
    #
    cD
    wcel
    #
    wa
    #
    cR
    vk
    vg
    cv
    #
    @8
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
    @0
    cfv
    #
    @8
    @15
    cmin
    cof
    #
    co
    #
    cZ
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
    cR
    vj
    @14
    vj
    cv
    #
    cX
    cfv
    #
    @8
    @24
    @17
    co
    #
    @2
    cfv
    #
    @20
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @8
    @1
    cfv
    @8
    @3
    cfv
    @10
    cR
    vk
    @14
    cR
    vj
    vh
    cv
    #
    @15
    @12
    wbr
    #
    vh
    cD
    crab
    #
    @25
    @15
    @24
    @17
    co
    #
    cY
    cfv
    #
    @26
    @34
    @17
    co
    #
    cZ
    cfv
    #
    @20
    co
    #
    @20
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
    cR
    vj
    @14
    cR
    vn
    @31
    @26
    @12
    wbr
    #
    vh
    cD
    crab
    #
    @25
    vn
    cv
    #
    cY
    cfv
    #
    @26
    @45
    @17
    co
    #
    cZ
    cfv
    #
    @20
    co
    #
    @20
    co
    #
    cmpt
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    @23
    @30
    @10
    vh
    vg
    @4
    cD
    @14
    vf
    vj
    vn
    vk
    @8
    cR
    cI
    cV
    @50
    @39
    psrass.d
    @14
    eqid
    wph
    cI
    cV
    wcel
    #
    @9
    psrring.i
    adantr
    wph
    @9
    simpr
    #
    @5
    wph
    cR
    ccmn
    wcel
    #
    @9
    wph
    cR
    crg
    wcel
    #
    @55
    psrring.r
    cR
    ringcmn
    syl
    adantr
    @10
    @24
    @14
    wcel
    #
    @45
    @44
    wcel
    #
    @50
    @4
    wcel
    #
    @10
    @57
    wa
    #
    @58
    wa
    #
    @56
    @25
    @4
    wcel
    #
    @49
    @4
    wcel
    #
    @59
    @60
    @56
    @58
    wph
    @56
    @9
    @57
    psrring.r
    ad2antrr
    #
    adantr
    #
    @60
    @62
    @58
    @60
    cD
    @4
    @24
    cX
    wph
    cD
    @4
    cX
    wf
    #
    @9
    @57
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @4
    cX
    psrring.s
    @5
    psrass.d
    psrass.b
    psrass.x
    psrelbas
    #
    ad2antrr
    @60
    @24
    cD
    wcel
    #
    @24
    @8
    @12
    wbr
    #
    @60
    @57
    @68
    @69
    wa
    @10
    @57
    simpr
    @13
    @69
    vg
    @24
    cD
    @11
    @24
    @8
    @12
    breq1
    elrab
    sylib
    #
    simpld
    #
    ffvelrnd
    #
    adantr
    @61
    @56
    @46
    @4
    wcel
    @48
    @4
    wcel
    @63
    @65
    @61
    cD
    @4
    @45
    cY
    wph
    cD
    @4
    cY
    wf
    #
    @9
    @57
    @58
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @4
    cY
    psrring.s
    @5
    psrass.d
    psrass.b
    psrass.y
    psrelbas
    #
    ad3antrrr
    @61
    @45
    cD
    wcel
    #
    @45
    @26
    @12
    wbr
    #
    @61
    @58
    @75
    @76
    wa
    @60
    @58
    simpr
    @43
    @76
    vh
    @45
    cD
    @31
    @45
    @26
    @12
    breq1
    elrab
    sylib
    #
    simpld
    #
    ffvelrnd
    @61
    cD
    @4
    @47
    cZ
    wph
    cD
    @4
    cZ
    wf
    #
    @9
    @57
    @58
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @4
    cZ
    psrring.s
    @5
    psrass.d
    psrass.b
    psrass.z
    psrelbas
    #
    ad3antrrr
    @61
    @47
    cD
    wcel
    #
    @47
    @26
    @12
    wbr
    #
    @61
    @53
    @26
    cD
    wcel
    #
    cI
    cn0
    @45
    wf
    #
    @76
    @81
    @82
    wa
    @60
    @53
    @58
    wph
    @53
    @9
    @57
    psrring.i
    ad2antrr
    #
    adantr
    #
    @60
    @83
    @58
    @60
    @83
    @26
    @8
    @12
    wbr
    #
    @60
    @53
    @9
    cI
    cn0
    @24
    wf
    #
    @69
    @83
    @87
    wa
    @85
    wph
    @9
    @57
    simplr
    @60
    @53
    @68
    @88
    @85
    @71
    cD
    vf
    @24
    cI
    cV
    psrass.d
    psrbagf
    #
    syl2anc
    @60
    @68
    @69
    @70
    simprd
    cD
    vf
    @8
    @24
    cI
    cV
    psrass.d
    psrbagcon
    syl13anc
    simpld
    #
    adantr
    @61
    @53
    @75
    @84
    @86
    @78
    cD
    vf
    @45
    cI
    cV
    psrass.d
    psrbagf
    syl2anc
    @61
    @75
    @76
    @77
    simprd
    cD
    vf
    @26
    @45
    cI
    cV
    psrass.d
    psrbagcon
    syl13anc
    simpld
    ffvelrnd
    @4
    cR
    @20
    @46
    @48
    @5
    @20
    eqid
    #
    ringcl
    syl3anc
    #
    @4
    cR
    @20
    @25
    @49
    @5
    @91
    ringcl
    syl3anc
    anasss
    @45
    @34
    wceq
    #
    @49
    @38
    @25
    @20
    @93
    @46
    @35
    @48
    @37
    @20
    @45
    @34
    cY
    fveq2
    @93
    @47
    @36
    cZ
    @45
    @34
    @26
    @17
    oveq2
    fveq2d
    oveq12d
    oveq2d
    psrass1lem
    @10
    @22
    @42
    cR
    cgsu
    @10
    vk
    @14
    @21
    @41
    @10
    @15
    @14
    wcel
    #
    wa
    #
    @21
    cR
    vj
    @33
    @25
    @35
    @20
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @19
    @20
    co
    cR
    vj
    @33
    @96
    @19
    @20
    co
    #
    cmpt
    #
    cgsu
    co
    @41
    @95
    @16
    @98
    @19
    @20
    @95
    vh
    cB
    cD
    cR
    cS
    c.xp
    @20
    vf
    vj
    cX
    cY
    cI
    @15
    psrring.s
    psrass.b
    @91
    psrass.t
    psrass.d
    wph
    cX
    cB
    wcel
    #
    @9
    @94
    psrass.x
    ad2antrr
    wph
    cY
    cB
    wcel
    #
    @9
    @94
    psrass.y
    ad2antrr
    @95
    @15
    cD
    wcel
    #
    @15
    @8
    @12
    wbr
    #
    @95
    @94
    @103
    @104
    wa
    @10
    @94
    simpr
    @13
    @104
    vg
    @15
    cD
    @11
    @15
    @8
    @12
    breq1
    elrab
    sylib
    #
    simpld
    #
    psrmulval
    oveq1d
    @95
    @33
    @4
    cR
    cplusg
    cfv
    #
    cR
    @20
    vj
    cfn
    @96
    @19
    cR
    c0g
    cfv
    #
    @5
    @108
    eqid
    #
    @107
    eqid
    #
    @91
    wph
    @56
    @9
    @94
    psrring.r
    ad2antrr
    #
    @95
    @53
    @103
    @33
    cfn
    wcel
    wph
    @53
    @9
    @94
    psrring.i
    ad2antrr
    #
    @106
    vh
    cD
    vf
    @15
    cI
    cV
    psrass.d
    psrbaglefi
    syl2anc
    #
    @95
    cD
    @4
    @18
    cZ
    wph
    @79
    @9
    @94
    @80
    ad2antrr
    @95
    @18
    cD
    wcel
    #
    @18
    @8
    @12
    wbr
    #
    @95
    @53
    @9
    cI
    cn0
    @15
    wf
    #
    @104
    @114
    @115
    wa
    @112
    wph
    @9
    @94
    simplr
    @95
    @53
    @103
    @116
    @112
    @106
    cD
    vf
    @15
    cI
    cV
    psrass.d
    psrbagf
    syl2anc
    #
    @95
    @103
    @104
    @105
    simprd
    cD
    vf
    @8
    @15
    cI
    cV
    psrass.d
    psrbagcon
    syl13anc
    simpld
    ffvelrnd
    #
    @95
    @24
    @33
    wcel
    #
    wa
    #
    @56
    @62
    @35
    @4
    wcel
    #
    @96
    @4
    wcel
    @95
    @56
    @119
    @111
    adantr
    #
    @120
    cD
    @4
    @24
    cX
    wph
    @66
    @9
    @94
    @119
    @67
    ad3antrrr
    @120
    @68
    @24
    @15
    @12
    wbr
    #
    @120
    @119
    @68
    @123
    wa
    @95
    @119
    simpr
    @32
    @123
    vh
    @24
    cD
    @31
    @24
    @15
    @12
    breq1
    elrab
    sylib
    #
    simpld
    #
    ffvelrnd
    #
    @120
    cD
    @4
    @34
    cY
    wph
    @73
    @9
    @94
    @119
    @74
    ad3antrrr
    @120
    @34
    cD
    wcel
    #
    @34
    @15
    @12
    wbr
    #
    @120
    @53
    @103
    @88
    @123
    @127
    @128
    wa
    @95
    @53
    @119
    @112
    adantr
    #
    @95
    @103
    @119
    @106
    adantr
    @120
    @53
    @68
    @88
    @129
    @125
    @89
    syl2anc
    #
    @120
    @68
    @123
    @124
    simprd
    cD
    vf
    @15
    @24
    cI
    cV
    psrass.d
    psrbagcon
    syl13anc
    simpld
    ffvelrnd
    #
    @4
    cR
    @20
    @25
    @35
    @5
    @91
    ringcl
    syl3anc
    #
    @95
    vj
    @33
    @97
    @4
    cvv
    @96
    @108
    @97
    eqid
    @113
    @132
    @108
    cvv
    wcel
    #
    @95
    cR
    c0g
    fvex
    #
    a1i
    fsuppmptdm
    gsummulc1
    @95
    @100
    @40
    cR
    cgsu
    @95
    vj
    @33
    @99
    @39
    @120
    @99
    @25
    @35
    @19
    @20
    co
    #
    @20
    co
    #
    @39
    @120
    @56
    @62
    @121
    @19
    @4
    wcel
    #
    @99
    @136
    wceq
    @122
    @126
    @131
    @95
    @137
    @119
    @118
    adantr
    @4
    cR
    @20
    @25
    @35
    @19
    @5
    @91
    ringass
    syl13anc
    @120
    @38
    @135
    @25
    @20
    @120
    @37
    @19
    @35
    @20
    @120
    @36
    @18
    cZ
    @120
    vz
    cI
    vz
    cv
    #
    @8
    cfv
    #
    @138
    @24
    cfv
    #
    cmin
    co
    #
    @138
    @15
    cfv
    #
    @140
    cmin
    co
    #
    cmin
    co
    #
    cmpt
    vz
    cI
    @139
    @142
    cmin
    co
    #
    cmpt
    @36
    @18
    @120
    vz
    cI
    @144
    @145
    @120
    @138
    cI
    wcel
    wa
    #
    @139
    cn0
    wcel
    #
    @142
    cn0
    wcel
    #
    @140
    cn0
    wcel
    #
    @144
    @145
    wceq
    #
    @120
    cI
    cn0
    @138
    @8
    @10
    cI
    cn0
    @8
    wf
    #
    @94
    @119
    wph
    @53
    @9
    @151
    psrring.i
    cD
    vf
    @8
    cI
    cV
    psrass.d
    psrbagf
    sylan
    ad2antrr
    #
    ffvelrnda
    #
    @120
    cI
    cn0
    @138
    @15
    @95
    @116
    @119
    @117
    adantr
    #
    ffvelrnda
    #
    @120
    cI
    cn0
    @138
    @24
    @130
    ffvelrnda
    #
    @147
    @139
    cc
    wcel
    @148
    @142
    cc
    wcel
    @149
    @140
    cc
    wcel
    @150
    @139
    nn0cn
    @142
    nn0cn
    @140
    nn0cn
    @139
    @142
    @140
    nnncan2
    syl3an
    syl3anc
    mpteq2dva
    @120
    vz
    cI
    @141
    @143
    cmin
    @26
    @34
    cV
    cvv
    cvv
    @129
    @146
    @139
    @140
    cmin
    ovexd
    @146
    @142
    @140
    cmin
    ovexd
    @120
    vz
    cI
    @139
    @140
    cmin
    @8
    @24
    cV
    cn0
    cn0
    @129
    @153
    @156
    @120
    vz
    cI
    cn0
    @8
    @152
    feqmptd
    #
    @120
    vz
    cI
    cn0
    @24
    @130
    feqmptd
    #
    offval2
    @120
    vz
    cI
    @142
    @140
    cmin
    @15
    @24
    cV
    cn0
    cn0
    @129
    @155
    @156
    @120
    vz
    cI
    cn0
    @15
    @154
    feqmptd
    #
    @158
    offval2
    offval2
    @120
    vz
    cI
    @139
    @142
    cmin
    @8
    @15
    cV
    cn0
    cn0
    @129
    @153
    @155
    @157
    @159
    offval2
    3eqtr4d
    fveq2d
    oveq2d
    oveq2d
    eqtr4d
    mpteq2dva
    oveq2d
    3eqtr2d
    mpteq2dva
    oveq2d
    @10
    @29
    @52
    cR
    cgsu
    @10
    vj
    @14
    @28
    @51
    @60
    @28
    @25
    cR
    vn
    @44
    @49
    cmpt
    #
    cgsu
    co
    #
    @20
    co
    @51
    @60
    @27
    @161
    @25
    @20
    @60
    vh
    cB
    cD
    cR
    cS
    c.xp
    @20
    vf
    vn
    cY
    cZ
    cI
    @26
    psrring.s
    psrass.b
    @91
    psrass.t
    psrass.d
    wph
    @102
    @9
    @57
    psrass.y
    ad2antrr
    wph
    cZ
    cB
    wcel
    #
    @9
    @57
    psrass.z
    ad2antrr
    @90
    psrmulval
    oveq2d
    @60
    @44
    @4
    @107
    cR
    @20
    vn
    cfn
    @49
    @25
    @108
    @5
    @109
    @110
    @91
    @64
    @60
    @53
    @83
    @44
    cfn
    wcel
    #
    @85
    @90
    vh
    cD
    vf
    @26
    cI
    cV
    psrass.d
    psrbaglefi
    syl2anc
    #
    @72
    @92
    @60
    @160
    cvv
    wcel
    #
    @160
    wfun
    #
    @133
    w3a
    #
    @163
    @160
    @108
    csupp
    co
    #
    @44
    wss
    #
    @160
    @108
    cfsupp
    wbr
    @167
    @60
    @165
    @166
    @133
    vn
    @44
    @49
    @43
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vh
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
    rab2ex
    mptex
    vn
    @44
    @49
    funmpt
    @134
    3pm3.2i
    a1i
    @164
    @169
    @60
    @168
    @160
    cdm
    @44
    @160
    @108
    suppssdm
    vn
    @44
    @49
    @160
    @160
    eqid
    dmmptss
    sstri
    a1i
    @44
    @160
    cvv
    cvv
    @108
    suppssfifsupp
    syl12anc
    gsummulc2
    eqtr4d
    mpteq2dva
    oveq2d
    3eqtr4d
    @10
    vg
    cB
    cD
    cR
    cS
    c.xp
    @20
    vf
    vk
    @0
    cZ
    cI
    @8
    psrring.s
    psrass.b
    @91
    psrass.t
    psrass.d
    wph
    @0
    cB
    wcel
    @9
    @6
    adantr
    wph
    @162
    @9
    psrass.z
    adantr
    @54
    psrmulval
    @10
    vg
    cB
    cD
    cR
    cS
    c.xp
    @20
    vf
    vj
    cX
    @2
    cI
    @8
    psrring.s
    psrass.b
    @91
    psrass.t
    psrass.d
    wph
    @101
    @9
    psrass.x
    adantr
    wph
    @2
    cB
    wcel
    @9
    @7
    adantr
    @54
    psrmulval
    3eqtr4d
    eqfnfvd
end
