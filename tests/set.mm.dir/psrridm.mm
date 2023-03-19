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
include "adantr.mm"
include "simpr.mm"
include "psrmulval.mm"
include "csn.mm"
include "cres.mm"
include "cn0.mm"
include "wf.mm"
include "psrbagf.mm"
include "sylan.mm"
include "nn0re.mm"
include "leidd.mm"
include "adantl.mm"
include "caofref.mm"
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
include "syl.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cmap.mm"
include "ovex.mm"
include "rab2ex.mm"
include "a1i.mm"
include "ad2antrr.mm"
include "sylib.mm"
include "simpld.mm"
include "ffvelrnd.mm"
include "syl2anc.mm"
include "simprd.mm"
include "psrbagcon.mm"
include "syl13anc.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "fmptd.mm"
include "cdif.mm"
include "cc0.mm"
include "cxp.mm"
include "wceq.mm"
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
include "wne.mm"
include "eldifsni.mm"
include "necomd.mm"
include "weq.mm"
include "wb.mm"
include "cc.mm"
include "wss.mm"
include "nn0sscn.mm"
include "fss.mm"
include "sylancl.mm"
include "ofsubeq0.mm"
include "necon3bbid.mm"
include "mpbird.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "ringrz.mm"
include "suppss2.mm"
include "wfun.mm"
include "csupp.mm"
include "cfsupp.mm"
include "mptexg.mm"
include "funmpt.mm"
include "snfi.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"
include "gsumres.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "mpbiri.mm"
include "fveq2d.mm"
include "fconstmpt.mm"
include "fczpsrbag.mm"
include "syl5eqel.mm"
include "iftrue.mm"
include "ffvelrnda.mm"
include "ringridm.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "gsumsn.mm"
include "3eqtr3d.mm"
include "3eqtrd.mm"
include "eqfnfvd.mm"

theorem psrridm
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
  assert |- ( ph -> ( X .x. U ) = X )

  proof
    wph
    vy
    cD
    cX
    cU
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
    cX
    cU
    psrring.s
    psr1cl.b
    psrlidm.t
    psrring.r
    psrlidm.x
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
    cX
    cfv
    #
    @5
    @12
    cmin
    cof
    #
    co
    #
    cU
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
    @5
    cX
    cfv
    #
    @5
    @5
    @14
    co
    #
    cU
    cfv
    #
    @17
    co
    #
    @21
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
    cX
    cU
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
    cX
    cB
    wcel
    @6
    psrlidm.x
    adantr
    wph
    cU
    cB
    wcel
    @6
    @3
    adantr
    #
    wph
    @6
    simpr
    #
    psrmulval
    @7
    cR
    @19
    @5
    csn
    #
    cres
    #
    cgsu
    co
    cR
    vz
    @28
    @18
    cmpt
    #
    cgsu
    co
    #
    @20
    @24
    @7
    @29
    @30
    cR
    cgsu
    @7
    vz
    @11
    @28
    @18
    @7
    @5
    @11
    @7
    @6
    @5
    @5
    @9
    wbr
    #
    @5
    @11
    wcel
    @27
    @7
    vz
    cI
    cle
    cn0
    @5
    cV
    wph
    cI
    cV
    wcel
    #
    @6
    psrring.i
    adantr
    #
    wph
    @33
    @6
    cI
    cn0
    @5
    wf
    #
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
    @12
    cn0
    wcel
    #
    @12
    @12
    cle
    wbr
    @7
    @37
    @12
    @12
    nn0re
    leidd
    adantl
    caofref
    @10
    @32
    vg
    @5
    cD
    @8
    @5
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
    @28
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
    @38
    psrring.r
    cR
    ringcmn
    syl
    adantr
    @11
    cvv
    wcel
    #
    @7
    @10
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vg
    vf
    cn0
    cI
    cmap
    co
    cD
    psr1cl.d
    cn0
    cI
    cmap
    ovex
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
    @39
    @13
    @1
    wcel
    #
    @16
    @1
    wcel
    @18
    @1
    wcel
    wph
    @39
    @6
    @42
    psrring.r
    ad2antrr
    #
    @43
    cD
    @1
    @12
    cX
    wph
    cD
    @1
    cX
    wf
    @6
    @42
    @4
    ad2antrr
    @43
    @12
    cD
    wcel
    #
    @12
    @5
    @9
    wbr
    #
    @43
    @42
    @46
    @47
    wa
    @7
    @42
    simpr
    @10
    @47
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
    ffvelrnd
    #
    @43
    cD
    @1
    @15
    cU
    @7
    cD
    @1
    cU
    wf
    @42
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
    @26
    psrelbas
    adantr
    @43
    @15
    cD
    wcel
    #
    @15
    @5
    @9
    wbr
    #
    @43
    @33
    @6
    cI
    cn0
    @12
    wf
    #
    @47
    @51
    @52
    wa
    wph
    @33
    @6
    @42
    psrring.i
    ad2antrr
    #
    @7
    @6
    @42
    @27
    adantr
    @43
    @33
    @46
    @53
    @54
    @49
    cD
    vf
    @12
    cI
    cV
    psr1cl.d
    psrbagf
    syl2anc
    #
    @43
    @46
    @47
    @48
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
    #
    ffvelrnd
    @1
    cR
    @17
    @13
    @16
    @2
    @25
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
    @28
    c.0
    @7
    @12
    @11
    @28
    cdif
    wcel
    #
    wa
    #
    @18
    @13
    c.0
    @17
    co
    #
    c.0
    @58
    @16
    c.0
    @13
    @17
    @58
    @16
    @15
    cI
    cc0
    csn
    cxp
    #
    wceq
    #
    c.1
    c.0
    cif
    #
    c.0
    @58
    @51
    @16
    @62
    wceq
    @57
    @7
    @42
    @51
    @12
    @11
    @28
    eldifi
    #
    @56
    sylan2
    vx
    @15
    vx
    cv
    #
    @60
    wceq
    #
    c.1
    c.0
    cif
    #
    @62
    cD
    cU
    @64
    @15
    wceq
    @65
    @61
    c.1
    c.0
    @64
    @15
    @60
    eqeq1
    ifbid
    psr1cl.u
    @61
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
    @58
    @61
    c.1
    c.0
    @58
    @61
    wn
    @5
    @12
    wne
    @58
    @12
    @5
    @57
    @12
    @5
    wne
    @7
    @12
    @11
    @5
    eldifsni
    adantl
    necomd
    @58
    @61
    @5
    @12
    @57
    @7
    @42
    @61
    vy
    vz
    weq
    wb
    #
    @63
    @43
    @33
    cI
    cc
    @5
    wf
    #
    cI
    cc
    @12
    wf
    #
    @69
    @54
    @7
    @70
    @42
    @7
    @35
    cn0
    cc
    wss
    #
    @70
    @36
    nn0sscn
    cI
    cn0
    cc
    @5
    fss
    sylancl
    #
    adantr
    @43
    @53
    @72
    @71
    @55
    nn0sscn
    cI
    cn0
    cc
    @12
    fss
    sylancl
    cI
    @5
    @12
    cV
    ofsubeq0
    syl3anc
    sylan2
    necon3bbid
    mpbird
    iffalsed
    eqtrd
    oveq2d
    @57
    @7
    @42
    @59
    c.0
    wceq
    #
    @63
    @43
    @39
    @44
    @74
    @45
    @50
    @1
    cR
    @17
    @13
    c.0
    @2
    @25
    psr1cl.z
    ringrz
    syl2anc
    sylan2
    eqtrd
    @41
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
    @28
    cfn
    wcel
    #
    @19
    c.0
    csupp
    co
    @28
    wss
    @19
    c.0
    cfsupp
    wbr
    @7
    @40
    @76
    @41
    vz
    @11
    @18
    cvv
    mptexg
    syl
    @77
    @7
    vz
    @11
    @18
    funmpt
    a1i
    @78
    @7
    @68
    a1i
    @79
    @7
    @5
    snfi
    a1i
    @75
    @28
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
    @6
    @24
    @1
    wcel
    @31
    @24
    wceq
    @7
    @39
    @80
    wph
    @39
    @6
    psrring.r
    adantr
    #
    cR
    ringmnd
    syl
    @27
    @7
    @24
    @21
    @1
    @7
    @24
    @21
    c.1
    @17
    co
    #
    @21
    @7
    @23
    c.1
    @21
    @17
    @7
    @23
    @60
    cU
    cfv
    #
    c.1
    @7
    @22
    @60
    cU
    @7
    @22
    @60
    wceq
    #
    vy
    vy
    weq
    #
    @5
    eqid
    @7
    @33
    @70
    @70
    @84
    @85
    wb
    @34
    @73
    @73
    cI
    @5
    @5
    cV
    ofsubeq0
    syl3anc
    mpbiri
    fveq2d
    @7
    @60
    cD
    wcel
    #
    @83
    c.1
    wceq
    wph
    @86
    @6
    wph
    @60
    vw
    cI
    cc0
    cmpt
    #
    cD
    vw
    cI
    cc0
    fconstmpt
    wph
    @33
    @87
    cD
    wcel
    psrring.i
    vw
    cD
    vf
    cI
    cV
    psr1cl.d
    fczpsrbag
    syl
    syl5eqel
    adantr
    vx
    @60
    @66
    c.1
    cD
    cU
    @65
    c.1
    c.0
    iftrue
    psr1cl.u
    @67
    fvmpt
    syl
    eqtrd
    oveq2d
    @7
    @39
    @21
    @1
    wcel
    @82
    @21
    wceq
    @81
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
    @21
    @2
    @25
    psr1cl.o
    ringridm
    syl2anc
    eqtrd
    #
    @88
    eqeltrd
    @18
    @1
    @24
    vz
    cR
    @5
    cD
    @2
    vz
    vy
    weq
    #
    @13
    @21
    @16
    @23
    @17
    @12
    @5
    cX
    fveq2
    @90
    @15
    @22
    cU
    @12
    @5
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
