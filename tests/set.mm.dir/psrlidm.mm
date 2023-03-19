include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "psr1cl.mm"
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
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "adantr.mm"
include "simpr.mm"
include "psrmulval.mm"
include "cres.mm"
include "fconstmpt.mm"
include "fczpsrbag.mm"
include "syl.mm"
include "syl5eqel.mm"
include "wral.mm"
include "cn0.mm"
include "wf.mm"
include "psrbagf.mm"
include "sylan.mm"
include "ffvelrnda.mm"
include "nn0ge0d.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "0nn0.mm"
include "fconst6.mm"
include "ffn.mm"
include "mp1i.mm"
include "inidm.mm"
include "wceq.mm"
include "a1i.mm"
include "fvconst2g.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "mpbird.mm"
include "breq1.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "snssd.mm"
include "resmptd.mm"
include "oveq2d.mm"
include "cvv.mm"
include "ccmn.mm"
include "crg.mm"
include "ringcmn.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cmap.mm"
include "ovex.mm"
include "rab2ex.mm"
include "ad2antrr.mm"
include "sylib.mm"
include "simpld.mm"
include "syldan.mm"
include "syl2anc.mm"
include "simprd.mm"
include "psrbagcon.mm"
include "syl13anc.mm"
include "ffvelrnd.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "fmptd.mm"
include "cdif.mm"
include "cif.mm"
include "eldifi.mm"
include "sylan2.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "cur.mm"
include "fvex.mm"
include "eqeltri.mm"
include "c0g.mm"
include "ifex.mm"
include "fvmpt.mm"
include "wn.mm"
include "eldifn.mm"
include "adantl.mm"
include "velsn.mm"
include "sylnib.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "ringlz.mm"
include "suppss2.mm"
include "wfun.mm"
include "csupp.mm"
include "wss.mm"
include "cfsupp.mm"
include "rabex2.mm"
include "mptrabex.mm"
include "funmpt.mm"
include "snfi.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"
include "gsumres.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "iftrue.mm"
include "nn0cn.mm"
include "subid1d.mm"
include "caofid0r.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "ringlidm.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "oveq2.mm"
include "gsumsn.mm"
include "3eqtr3d.mm"
include "3eqtrd.mm"
include "eqfnfvd.mm"

theorem psrlidm
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let vf: setvar f
  let cI: class I
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let vk: setvar k
  let c.pl: class .+
  let vy: setvar y
  let vz: setvar z
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
  let cZ: class Z
  let c.xp: class .X.
  let cY: class Y
  assume psrring.s: |- S = ( I mPwSer R )
  assume psrring.i: |- ( ph -> I e. V )
  assume psrring.r: |- ( ph -> R e. Ring )
  assume psr1cl.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume psr1cl.z: |- .0. = ( 0g ` R )
  assume psr1cl.o: |- .1. = ( 1r ` R )
  assume psr1cl.u: |- U = ( x e. D |-> if ( x = ( I X. { 0 } ) , .1. , .0. ) )
  assume psr1cl.b: |- B = ( Base ` S )
  assume psrlidm.t: |- .x. = ( .r ` S )
  assume psrlidm.x: |- ( ph -> X e. B )

  disjoint f x
  disjoint .0. f
  disjoint .0. x
  disjoint I f
  disjoint I x
  disjoint B x
  disjoint R f
  disjoint R x
  disjoint D x
  disjoint X f
  disjoint X x
  disjoint ph x
  disjoint V x
  disjoint .x. x
  disjoint S x
  disjoint .1. x
  disjoint k x
  disjoint .+ k
  disjoint .+ x
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
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
  disjoint ph y
  disjoint ph z
  disjoint V g
  disjoint V h
  disjoint V j
  disjoint V k
  disjoint V r
  disjoint V w
  disjoint V y
  disjoint .x. k
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
  disjoint S y
  disjoint S z
  disjoint .1. y
  disjoint .X. j
  disjoint .X. k
  disjoint .X. x
  disjoint Y f
  disjoint Y g
  disjoint Y h
  disjoint Y j
  disjoint Y k
  disjoint Y n
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  assert |- ( ph -> ( U .x. X ) = X )

  proof
    wph
    vy
    cD
    cU
    cX
    c.x
    co
    #
    cX
    wph
    cD
    cR
    cbs
    cfv
    #
    @0
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @1
    @0
    psrring.s
    @1
    eqid
    #
    psr1cl.d
    psr1cl.b
    wph
    cB
    cR
    cS
    c.x
    cI
    cU
    cX
    psrring.s
    psr1cl.b
    psrlidm.t
    psrring.r
    wph
    vx
    cB
    cD
    cR
    cS
    cU
    c.1
    vf
    cI
    cV
    c.0
    psrring.s
    psrring.i
    psrring.r
    psr1cl.d
    psr1cl.z
    psr1cl.o
    psr1cl.u
    psr1cl.b
    psr1cl
    #
    psrlidm.x
    psrmulcl
    psrelbas
    ffnd
    wph
    cD
    @1
    cX
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @1
    cX
    psrring.s
    @2
    psr1cl.d
    psr1cl.b
    psrlidm.x
    psrelbas
    #
    ffnd
    wph
    vy
    cv
    #
    cD
    wcel
    #
    wa
    #
    @5
    @0
    cfv
    cR
    vz
    vg
    cv
    #
    @5
    cle
    cofr
    #
    wbr
    #
    vg
    cD
    crab
    #
    vz
    cv
    #
    cU
    cfv
    #
    @5
    @12
    cmin
    cof
    #
    co
    #
    cX
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
    cI
    cc0
    csn
    cxp
    #
    cU
    cfv
    #
    @5
    @21
    @14
    co
    #
    cX
    cfv
    #
    @17
    co
    #
    @5
    cX
    cfv
    #
    @7
    vg
    cB
    cD
    cR
    cS
    c.x
    @17
    vf
    vz
    cU
    cX
    cI
    @5
    psrring.s
    psr1cl.b
    @17
    eqid
    #
    psrlidm.t
    psr1cl.d
    wph
    cU
    cB
    wcel
    @6
    @3
    adantr
    #
    wph
    cX
    cB
    wcel
    @6
    psrlidm.x
    adantr
    wph
    @6
    simpr
    #
    psrmulval
    @7
    cR
    @19
    @21
    csn
    #
    cres
    #
    cgsu
    co
    cR
    vz
    @30
    @18
    cmpt
    #
    cgsu
    co
    #
    @20
    @25
    @7
    @31
    @32
    cR
    cgsu
    @7
    vz
    @11
    @30
    @18
    @7
    @21
    @11
    @7
    @21
    cD
    wcel
    #
    @21
    @5
    @9
    wbr
    #
    @21
    @11
    wcel
    wph
    @34
    @6
    wph
    @21
    vx
    cI
    cc0
    cmpt
    #
    cD
    vx
    cI
    cc0
    fconstmpt
    wph
    cI
    cV
    wcel
    #
    @36
    cD
    wcel
    psrring.i
    vx
    cD
    vf
    cI
    cV
    psr1cl.d
    fczpsrbag
    syl
    syl5eqel
    adantr
    #
    @7
    @35
    cc0
    vx
    cv
    #
    @5
    cfv
    #
    cle
    wbr
    #
    vx
    cI
    wral
    @7
    @41
    vx
    cI
    @7
    @39
    cI
    wcel
    #
    wa
    #
    @40
    @7
    cI
    cn0
    @39
    @5
    wph
    @37
    @6
    cI
    cn0
    @5
    wf
    psrring.i
    cD
    vf
    @5
    cI
    cV
    psr1cl.d
    psrbagf
    sylan
    #
    ffvelrnda
    nn0ge0d
    ralrimiva
    @7
    vx
    cI
    cI
    cc0
    @40
    cle
    cI
    @21
    @5
    cV
    cV
    cI
    cn0
    @21
    wf
    @21
    cI
    wfn
    @7
    cI
    cc0
    cn0
    0nn0
    fconst6
    cI
    cn0
    @21
    ffn
    mp1i
    @7
    cI
    cn0
    @5
    @44
    ffnd
    wph
    @37
    @6
    psrring.i
    adantr
    #
    @45
    cI
    inidm
    @7
    cc0
    cn0
    wcel
    #
    @42
    @39
    @21
    cfv
    cc0
    wceq
    @46
    @7
    0nn0
    a1i
    #
    cI
    cc0
    @39
    cn0
    fvconst2g
    sylan
    @43
    @40
    eqidd
    ofrfval
    mpbird
    @10
    @35
    vg
    @21
    cD
    @8
    @21
    @5
    @9
    breq1
    elrab
    sylanbrc
    snssd
    resmptd
    oveq2d
    @7
    @11
    @1
    @19
    cR
    cvv
    @30
    c.0
    @2
    psr1cl.z
    wph
    cR
    ccmn
    wcel
    #
    @6
    wph
    cR
    crg
    wcel
    #
    @48
    psrring.r
    cR
    ringcmn
    syl
    adantr
    @11
    cvv
    wcel
    @7
    @10
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    vg
    vf
    cn0
    cI
    cmap
    co
    #
    cD
    psr1cl.d
    cn0
    cI
    cmap
    ovex
    #
    rab2ex
    a1i
    #
    @7
    vz
    @11
    @18
    @1
    @19
    @7
    @12
    @11
    wcel
    #
    wa
    #
    @49
    @13
    @1
    wcel
    #
    @16
    @1
    wcel
    #
    @18
    @1
    wcel
    wph
    @49
    @6
    @54
    psrring.r
    ad2antrr
    @7
    @54
    @12
    cD
    wcel
    #
    @56
    @55
    @58
    @12
    @5
    @9
    wbr
    #
    @55
    @54
    @58
    @59
    wa
    #
    @7
    @54
    simpr
    @10
    @59
    vg
    @12
    cD
    @8
    @12
    @5
    @9
    breq1
    elrab
    sylib
    #
    simpld
    #
    @7
    cD
    @1
    @12
    cU
    @7
    cB
    cD
    cR
    cS
    vf
    cI
    @1
    cU
    psrring.s
    @2
    psr1cl.d
    psr1cl.b
    @28
    psrelbas
    ffvelrnda
    syldan
    @55
    cD
    @1
    @15
    cX
    wph
    cD
    @1
    cX
    wf
    @6
    @54
    @4
    ad2antrr
    @55
    @15
    cD
    wcel
    #
    @15
    @5
    @9
    wbr
    #
    @55
    @37
    @6
    cI
    cn0
    @12
    wf
    #
    @59
    @63
    @64
    wa
    wph
    @37
    @6
    @54
    psrring.i
    ad2antrr
    #
    @7
    @6
    @54
    @29
    adantr
    @55
    @37
    @58
    @65
    @66
    @62
    cD
    vf
    @12
    cI
    cV
    psr1cl.d
    psrbagf
    syl2anc
    @55
    @58
    @59
    @61
    simprd
    cD
    vf
    @5
    @12
    cI
    cV
    psr1cl.d
    psrbagcon
    syl13anc
    simpld
    ffvelrnd
    #
    @1
    cR
    @17
    @13
    @16
    @2
    @27
    ringcl
    syl3anc
    @19
    eqid
    fmptd
    @7
    @11
    @18
    vz
    cvv
    @30
    c.0
    @7
    @12
    @11
    @30
    cdif
    wcel
    #
    wa
    #
    @18
    c.0
    @16
    @17
    co
    #
    c.0
    @69
    @13
    c.0
    @16
    @17
    @69
    @13
    @12
    @21
    wceq
    #
    c.1
    c.0
    cif
    #
    c.0
    @69
    @58
    @13
    @72
    wceq
    @69
    @58
    @59
    @68
    @7
    @54
    @60
    @12
    @11
    @30
    eldifi
    #
    @61
    sylan2
    simpld
    vx
    @12
    @39
    @21
    wceq
    #
    c.1
    c.0
    cif
    #
    @72
    cD
    cU
    @39
    @12
    wceq
    @74
    @71
    c.1
    c.0
    @39
    @12
    @21
    eqeq1
    ifbid
    psr1cl.u
    @71
    c.1
    c.0
    c.1
    cR
    cur
    cfv
    cvv
    psr1cl.o
    cR
    cur
    fvex
    eqeltri
    #
    c.0
    cR
    c0g
    cfv
    cvv
    psr1cl.z
    cR
    c0g
    fvex
    eqeltri
    #
    ifex
    fvmpt
    syl
    @69
    @71
    c.1
    c.0
    @69
    @12
    @30
    wcel
    #
    @71
    @68
    @78
    wn
    @7
    @12
    @11
    @30
    eldifn
    adantl
    vz
    @21
    velsn
    sylnib
    iffalsed
    eqtrd
    oveq1d
    @69
    @49
    @57
    @70
    c.0
    wceq
    wph
    @49
    @6
    @68
    psrring.r
    ad2antrr
    @68
    @7
    @54
    @57
    @73
    @67
    sylan2
    @1
    cR
    @17
    @16
    c.0
    @2
    @27
    psr1cl.z
    ringlz
    syl2anc
    eqtrd
    @53
    suppss2
    #
    @7
    @19
    cvv
    wcel
    #
    @19
    wfun
    #
    c.0
    cvv
    wcel
    #
    @30
    cfn
    wcel
    #
    @19
    c.0
    csupp
    co
    @30
    wss
    @19
    c.0
    cfsupp
    wbr
    @80
    @7
    @10
    vz
    vg
    cD
    @18
    @50
    vf
    @51
    cD
    psr1cl.d
    @52
    rabex2
    mptrabex
    a1i
    @81
    @7
    vz
    @11
    @18
    funmpt
    a1i
    @82
    @7
    @77
    a1i
    @83
    @7
    @21
    snfi
    a1i
    @79
    @30
    @19
    cvv
    cvv
    c.0
    suppssfifsupp
    syl32anc
    gsumres
    @7
    cR
    cmnd
    wcel
    #
    @34
    @25
    @1
    wcel
    @33
    @25
    wceq
    @7
    @49
    @84
    wph
    @49
    @6
    psrring.r
    adantr
    #
    cR
    ringmnd
    syl
    @38
    @7
    @25
    @26
    @1
    @7
    @25
    c.1
    @26
    @17
    co
    #
    @26
    @7
    @22
    c.1
    @24
    @26
    @17
    @7
    @34
    @22
    c.1
    wceq
    @38
    vx
    @21
    @75
    c.1
    cD
    cU
    @74
    c.1
    c.0
    iftrue
    psr1cl.u
    @76
    fvmpt
    syl
    @7
    @23
    @5
    cX
    @7
    vz
    cI
    cc0
    cmin
    cn0
    @5
    cV
    cn0
    @45
    @44
    @47
    @12
    cn0
    wcel
    #
    @12
    cc0
    cmin
    co
    @12
    wceq
    @7
    @87
    @12
    @12
    nn0cn
    subid1d
    adantl
    caofid0r
    fveq2d
    oveq12d
    @7
    @49
    @26
    @1
    wcel
    @86
    @26
    wceq
    @85
    wph
    cD
    @1
    @5
    cX
    @4
    ffvelrnda
    #
    @1
    cR
    @17
    c.1
    @26
    @2
    @27
    psr1cl.o
    ringlidm
    syl2anc
    eqtrd
    #
    @88
    eqeltrd
    @18
    @1
    @25
    vz
    cR
    @21
    cD
    @2
    @71
    @13
    @22
    @16
    @24
    @17
    @12
    @21
    cU
    fveq2
    @71
    @15
    @23
    cX
    @12
    @21
    @5
    @14
    oveq2
    fveq2d
    oveq12d
    gsumsn
    syl3anc
    3eqtr3d
    @89
    3eqtrd
    eqfnfvd
end
