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
include "cplusg.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "eqid.mm"
include "psradd.mm"
include "fveq1d.mm"
include "ad2antrr.mm"
include "ssrab2.mm"
include "simpr.mm"
include "sseldi.mm"
include "cvv.mm"
include "cbs.mm"
include "wf.mm"
include "psrelbas.mm"
include "ffnd.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "ovex.mm"
include "rabex2.mm"
include "a1i.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofval.mm"
include "mpdan.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "crg.mm"
include "ffvelrnd.mm"
include "simplr.mm"
include "psrbagconcl.mm"
include "syl3anc.mm"
include "ringdir.mm"
include "syl13anc.mm"
include "mpteq2dva.mm"
include "psrbaglefi.mm"
include "sylan.mm"
include "ringcl.mm"
include "offval2.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "ccmn.mm"
include "adantr.mm"
include "ringcmn.mm"
include "syl.mm"
include "gsummptfidmadd2.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "psraddcl.mm"
include "psrmulfval.mm"
include "psrmulcl.mm"
include "ovexd.mm"
include "3eqtr4d.mm"

theorem psrdir
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.pl: class .+
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
  assume psrdi.a: |- .+ = ( +g ` S )

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
  assert |- ( ph -> ( ( X .+ Y ) .X. Z ) = ( ( X .X. Z ) .+ ( Y .X. Z ) ) )

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
    cX
    cY
    c.pl
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
    cmpt
    vk
    cD
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
    cR
    vx
    @2
    @3
    cY
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
    cR
    cplusg
    cfv
    #
    co
    #
    cmpt
    #
    @4
    cZ
    c.xp
    co
    cX
    cZ
    c.xp
    co
    #
    cY
    cZ
    c.xp
    co
    #
    c.pl
    co
    #
    wph
    vk
    cD
    @11
    @21
    wph
    @0
    cD
    wcel
    #
    wa
    #
    @11
    cR
    @14
    @18
    @20
    cof
    #
    co
    #
    cgsu
    co
    @21
    @27
    @10
    @29
    cR
    cgsu
    @27
    @10
    vx
    @2
    @13
    @17
    @20
    co
    #
    cmpt
    @29
    @27
    vx
    @2
    @9
    @30
    @27
    @3
    @2
    wcel
    #
    wa
    #
    @9
    @12
    @16
    @20
    co
    #
    @7
    @8
    co
    #
    @30
    @32
    @5
    @33
    @7
    @8
    @32
    @5
    @3
    cX
    cY
    @28
    co
    #
    cfv
    #
    @33
    wph
    @5
    @36
    wceq
    @26
    @31
    wph
    @3
    @4
    @35
    wph
    cB
    @20
    c.pl
    cR
    cS
    cI
    cX
    cY
    psrring.s
    psrass.b
    @20
    eqid
    #
    psrdi.a
    psrass.x
    psrass.y
    psradd
    fveq1d
    ad2antrr
    @32
    @3
    cD
    wcel
    #
    @36
    @33
    wceq
    @32
    @2
    cD
    @3
    @1
    vy
    cD
    ssrab2
    #
    @27
    @31
    simpr
    #
    sseldi
    #
    @32
    cD
    cD
    @12
    @16
    @20
    cD
    cX
    cY
    cvv
    cvv
    @3
    @32
    cD
    cR
    cbs
    cfv
    #
    cX
    wph
    cD
    @42
    cX
    wf
    @26
    @31
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @42
    cX
    psrring.s
    @42
    eqid
    #
    psrass.d
    psrass.b
    psrass.x
    psrelbas
    ad2antrr
    #
    ffnd
    @32
    cD
    @42
    cY
    wph
    cD
    @42
    cY
    wf
    @26
    @31
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @42
    cY
    psrring.s
    @43
    psrass.d
    psrass.b
    psrass.y
    psrelbas
    ad2antrr
    #
    ffnd
    cD
    cvv
    wcel
    #
    @32
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
    a1i
    #
    @48
    cD
    inidm
    @32
    @38
    wa
    #
    @12
    eqidd
    @49
    @16
    eqidd
    ofval
    mpdan
    eqtrd
    oveq1d
    @32
    cR
    crg
    wcel
    #
    @12
    @42
    wcel
    #
    @16
    @42
    wcel
    #
    @7
    @42
    wcel
    #
    @34
    @30
    wceq
    wph
    @50
    @26
    @31
    psrring.r
    ad2antrr
    #
    @32
    cD
    @42
    @3
    cX
    @44
    @41
    ffvelrnd
    #
    @32
    cD
    @42
    @3
    cY
    @45
    @41
    ffvelrnd
    #
    @32
    cD
    @42
    @6
    cZ
    wph
    cD
    @42
    cZ
    wf
    @26
    @31
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @42
    cZ
    psrring.s
    @43
    psrass.d
    psrass.b
    psrass.z
    psrelbas
    ad2antrr
    @32
    @2
    cD
    @6
    @39
    @32
    cI
    cV
    wcel
    #
    @26
    @31
    @6
    @2
    wcel
    wph
    @57
    @26
    @31
    psrring.i
    ad2antrr
    wph
    @26
    @31
    simplr
    @40
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
    @42
    @20
    cR
    @8
    @12
    @16
    @7
    @43
    @37
    @8
    eqid
    #
    ringdir
    syl13anc
    eqtrd
    mpteq2dva
    @27
    vx
    @2
    @13
    @17
    @20
    @14
    @18
    cfn
    @42
    @42
    wph
    @57
    @26
    @2
    cfn
    wcel
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
    @32
    @50
    @51
    @53
    @13
    @42
    wcel
    @54
    @55
    @58
    @42
    cR
    @8
    @12
    @7
    @43
    @59
    ringcl
    syl3anc
    #
    @32
    @50
    @52
    @53
    @17
    @42
    wcel
    @54
    @56
    @58
    @42
    cR
    @8
    @16
    @7
    @43
    @59
    ringcl
    syl3anc
    #
    @27
    @14
    eqidd
    @27
    @18
    eqidd
    offval2
    eqtr4d
    oveq2d
    @27
    vx
    @2
    @42
    @13
    @17
    @20
    @14
    cR
    @18
    @43
    @37
    @27
    @50
    cR
    ccmn
    wcel
    wph
    @50
    @26
    psrring.r
    adantr
    cR
    ringcmn
    syl
    @60
    @61
    @62
    @14
    eqid
    @18
    eqid
    gsummptfidmadd2
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
    cZ
    cI
    psrring.s
    psrass.b
    @59
    psrass.t
    psrass.d
    wph
    cB
    c.pl
    cR
    cS
    cI
    cX
    cY
    psrring.s
    psrass.b
    psrdi.a
    wph
    @50
    cR
    cgrp
    wcel
    psrring.r
    cR
    ringgrp
    syl
    psrass.x
    psrass.y
    psraddcl
    psrass.z
    psrmulfval
    wph
    @25
    @23
    @24
    @28
    co
    @22
    wph
    cB
    @20
    c.pl
    cR
    cS
    cI
    @23
    @24
    psrring.s
    psrass.b
    @37
    psrdi.a
    wph
    cB
    cR
    cS
    c.xp
    cI
    cX
    cZ
    psrring.s
    psrass.b
    psrass.t
    psrring.r
    psrass.x
    psrass.z
    psrmulcl
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
    psradd
    wph
    vk
    cD
    @15
    @19
    @20
    @23
    @24
    cvv
    cvv
    cvv
    @46
    wph
    @47
    a1i
    @27
    cR
    @14
    cgsu
    ovexd
    @27
    cR
    @18
    cgsu
    ovexd
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
    cZ
    cI
    psrring.s
    psrass.b
    @59
    psrass.t
    psrass.d
    psrass.x
    psrass.z
    psrmulfval
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
    cY
    cZ
    cI
    psrring.s
    psrass.b
    @59
    psrass.t
    psrass.d
    psrass.y
    psrass.z
    psrmulfval
    offval2
    eqtrd
    3eqtr4d
end
