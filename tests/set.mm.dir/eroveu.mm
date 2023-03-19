include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "co.mm"
include "wrex.mm"
include "wex.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "weu.mm"
include "cqs.mm"
include "elqsi.mm"
include "eleq2s.mm"
include "anim12i.mm"
include "adantl.mm"
include "reeanv.mm"
include "sylibr.mm"
include "cvv.mm"
include "adantr.mm"
include "ecexg.mm"
include "elisset.mm"
include "3syl.mm"
include "biantrud.mm"
include "2rexbidv.mm"
include "mpbid.mm"
include "19.42v.mm"
include "bicomi.mm"
include "rexbii.mm"
include "rexcom4.mm"
include "bitri.mm"
include "sylib.mm"
include "eceq1.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "oveq1.mm"
include "eceq1d.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "cbvrex2v.mm"
include "anbi12i.mm"
include "bitr4i.mm"
include "wbr.mm"
include "wer.mm"
include "wss.mm"
include "simprll.mm"
include "sseldd.mm"
include "erth.mm"
include "simprrl.mm"
include "cxp.mm"
include "wf.mm"
include "fovrnd.mm"
include "3imtr3d.mm"
include "eqeq2.mm"
include "biimprcd.mm"
include "syl6.mm"
include "impd.mm"
include "wb.mm"
include "eqeq1.mm"
include "bi2anan9.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "anassrs.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "alrimivv.mm"
include "eu4.mm"
include "sylanbrc.mm"

theorem eroveu
  let wph: wff ph
  let vz: setvar z
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cJ: class J
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let cL: class L
  let cP: class P
  let cQ: class Q
  assume eropr.1: |- J = ( A /. R )
  assume eropr.2: |- K = ( B /. S )
  assume eropr.3: |- ( ph -> T e. Z )
  assume eropr.4: |- ( ph -> R Er U )
  assume eropr.5: |- ( ph -> S Er V )
  assume eropr.6: |- ( ph -> T Er W )
  assume eropr.7: |- ( ph -> A C_ U )
  assume eropr.8: |- ( ph -> B C_ V )
  assume eropr.9: |- ( ph -> C C_ W )
  assume eropr.10: |- ( ph -> .+ : ( A X. B ) --> C )
  assume eropr.11: |- ( ( ph /\ ( ( r e. A /\ s e. A ) /\ ( t e. B /\ u e. B ) ) ) -> ( ( r R s /\ t S u ) -> ( r .+ t ) T ( s .+ u ) ) )

  disjoint p q
  disjoint p r
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p z
  disjoint A p
  disjoint q r
  disjoint q s
  disjoint q t
  disjoint q u
  disjoint q z
  disjoint A q
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r z
  disjoint A r
  disjoint s t
  disjoint s u
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t z
  disjoint A t
  disjoint u z
  disjoint A u
  disjoint A z
  disjoint B p
  disjoint B q
  disjoint B r
  disjoint B s
  disjoint B t
  disjoint B u
  disjoint B z
  disjoint J p
  disjoint J q
  disjoint J z
  disjoint R p
  disjoint R q
  disjoint R r
  disjoint R s
  disjoint R t
  disjoint R u
  disjoint R z
  disjoint K p
  disjoint K q
  disjoint K z
  disjoint S p
  disjoint S q
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S z
  disjoint .+ p
  disjoint .+ q
  disjoint .+ r
  disjoint .+ s
  disjoint .+ t
  disjoint .+ u
  disjoint .+ z
  disjoint p ph
  disjoint ph q
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph z
  disjoint T p
  disjoint T q
  disjoint T r
  disjoint T s
  disjoint T t
  disjoint T u
  disjoint T z
  disjoint X p
  disjoint X q
  disjoint X r
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X z
  disjoint Y p
  disjoint Y q
  disjoint Y r
  disjoint Y s
  disjoint Y t
  disjoint Y u
  disjoint Y z
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint L p
  disjoint L q
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint P p
  disjoint P q
  disjoint P r
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint Q p
  disjoint Q q
  disjoint Q r
  disjoint Q s
  disjoint Q t
  disjoint Q u
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint .+ w
  disjoint .+ x
  disjoint .+ y
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint X w
  disjoint Y w
  assert |- ( ( ph /\ ( X e. J /\ Y e. K ) ) -> E! z E. p e. A E. q e. B ( ( X = [ p ] R /\ Y = [ q ] S ) /\ z = [ ( p .+ q ) ] T ) )

  proof
    wph
    cX
    cJ
    wcel
    #
    cY
    cK
    wcel
    #
    wa
    #
    wa
    #
    cX
    vp
    cv
    #
    cR
    cec
    #
    wceq
    #
    cY
    vq
    cv
    #
    cS
    cec
    #
    wceq
    #
    wa
    #
    vz
    cv
    #
    @4
    @7
    c.pl
    co
    #
    cT
    cec
    #
    wceq
    #
    wa
    #
    vq
    cB
    wrex
    #
    vp
    cA
    wrex
    #
    vz
    wex
    #
    @17
    @10
    vw
    cv
    #
    @13
    wceq
    #
    wa
    #
    vq
    cB
    wrex
    vp
    cA
    wrex
    #
    wa
    #
    vz
    vw
    weq
    #
    wi
    #
    vw
    wal
    vz
    wal
    @17
    vz
    weu
    @3
    @10
    @14
    vz
    wex
    #
    wa
    #
    vq
    cB
    wrex
    #
    vp
    cA
    wrex
    #
    @18
    @3
    @10
    vq
    cB
    wrex
    vp
    cA
    wrex
    #
    @29
    @3
    @6
    vp
    cA
    wrex
    #
    @9
    vq
    cB
    wrex
    #
    wa
    #
    @30
    @2
    @33
    wph
    @0
    @31
    @1
    @32
    @31
    cX
    cA
    cR
    cqs
    cJ
    vp
    cA
    cX
    cR
    elqsi
    eropr.1
    eleq2s
    @32
    cY
    cB
    cS
    cqs
    cK
    vq
    cB
    cY
    cS
    elqsi
    eropr.2
    eleq2s
    anim12i
    adantl
    @6
    @9
    vp
    vq
    cA
    cB
    reeanv
    sylibr
    @3
    @10
    @27
    vp
    vq
    cA
    cB
    @3
    @26
    @10
    @3
    cT
    cZ
    wcel
    #
    @13
    cvv
    wcel
    @26
    wph
    @34
    @2
    eropr.3
    adantr
    @12
    cZ
    cT
    ecexg
    vz
    @13
    cvv
    elisset
    3syl
    biantrud
    2rexbidv
    mpbid
    @29
    @16
    vz
    wex
    #
    vp
    cA
    wrex
    @18
    @28
    @35
    vp
    cA
    @28
    @15
    vz
    wex
    #
    vq
    cB
    wrex
    @35
    @27
    @36
    vq
    cB
    @36
    @27
    @10
    @14
    vz
    19.42v
    bicomi
    rexbii
    @15
    vq
    vz
    cB
    rexcom4
    bitri
    rexbii
    @16
    vp
    vz
    cA
    rexcom4
    bitri
    sylib
    @3
    @25
    vz
    vw
    wph
    @25
    @2
    @23
    cX
    vr
    cv
    #
    cR
    cec
    #
    wceq
    #
    cY
    vt
    cv
    #
    cS
    cec
    #
    wceq
    #
    wa
    #
    @11
    @37
    @40
    c.pl
    co
    #
    cT
    cec
    #
    wceq
    #
    wa
    #
    vt
    cB
    wrex
    #
    cX
    vs
    cv
    #
    cR
    cec
    #
    wceq
    #
    cY
    vu
    cv
    #
    cS
    cec
    #
    wceq
    #
    wa
    #
    @19
    @49
    @52
    c.pl
    co
    #
    cT
    cec
    #
    wceq
    #
    wa
    #
    vu
    cB
    wrex
    #
    wa
    #
    vs
    cA
    wrex
    vr
    cA
    wrex
    #
    wph
    @24
    @62
    @48
    vr
    cA
    wrex
    #
    @60
    vs
    cA
    wrex
    #
    wa
    @23
    @48
    @60
    vr
    vs
    cA
    cA
    reeanv
    @17
    @63
    @22
    @64
    @15
    @47
    @39
    @9
    wa
    #
    @11
    @37
    @7
    c.pl
    co
    #
    cT
    cec
    #
    wceq
    #
    wa
    vp
    vq
    vr
    vt
    cA
    cB
    vp
    vr
    weq
    #
    @10
    @65
    @14
    @68
    @69
    @6
    @39
    @9
    @69
    @5
    @38
    cX
    @4
    @37
    cR
    eceq1
    eqeq2d
    anbi1d
    @69
    @13
    @67
    @11
    @69
    @12
    @66
    cT
    @4
    @37
    @7
    c.pl
    oveq1
    eceq1d
    eqeq2d
    anbi12d
    vq
    vt
    weq
    #
    @65
    @43
    @68
    @46
    @70
    @9
    @42
    @39
    @70
    @8
    @41
    cY
    @7
    @40
    cS
    eceq1
    eqeq2d
    anbi2d
    @70
    @67
    @45
    @11
    @70
    @66
    @44
    cT
    @7
    @40
    @37
    c.pl
    oveq2
    eceq1d
    eqeq2d
    anbi12d
    cbvrex2v
    @21
    @59
    @51
    @9
    wa
    #
    @19
    @49
    @7
    c.pl
    co
    #
    cT
    cec
    #
    wceq
    #
    wa
    vp
    vq
    vs
    vu
    cA
    cB
    vp
    vs
    weq
    #
    @10
    @71
    @20
    @74
    @75
    @6
    @51
    @9
    @75
    @5
    @50
    cX
    @4
    @49
    cR
    eceq1
    eqeq2d
    anbi1d
    @75
    @13
    @73
    @19
    @75
    @12
    @72
    cT
    @4
    @49
    @7
    c.pl
    oveq1
    eceq1d
    eqeq2d
    anbi12d
    vq
    vu
    weq
    #
    @71
    @55
    @74
    @58
    @76
    @9
    @54
    @51
    @76
    @8
    @53
    cY
    @7
    @52
    cS
    eceq1
    eqeq2d
    anbi2d
    @76
    @73
    @57
    @19
    @76
    @72
    @56
    cT
    @7
    @52
    @49
    c.pl
    oveq2
    eceq1d
    eqeq2d
    anbi12d
    cbvrex2v
    anbi12i
    bitr4i
    wph
    @61
    @24
    vr
    vs
    cA
    cA
    @61
    @47
    @59
    wa
    #
    vu
    cB
    wrex
    vt
    cB
    wrex
    wph
    @37
    cA
    wcel
    #
    @49
    cA
    wcel
    #
    wa
    #
    wa
    #
    @24
    @47
    @59
    vt
    vu
    cB
    cB
    reeanv
    @81
    @77
    @24
    vt
    vu
    cB
    cB
    wph
    @80
    @40
    cB
    wcel
    #
    @52
    cB
    wcel
    #
    wa
    #
    @77
    @24
    wi
    wph
    @80
    @84
    wa
    #
    wa
    #
    @47
    @59
    @24
    @86
    @59
    @24
    wi
    @47
    @38
    @50
    wceq
    #
    @41
    @53
    wceq
    #
    wa
    #
    @58
    wa
    #
    @45
    @19
    wceq
    #
    wi
    @86
    @89
    @58
    @91
    @86
    @89
    @45
    @57
    wceq
    #
    @58
    @91
    wi
    @86
    @37
    @49
    cR
    wbr
    #
    @40
    @52
    cS
    wbr
    #
    wa
    @44
    @56
    cT
    wbr
    @89
    @92
    eropr.11
    @86
    @93
    @87
    @94
    @88
    @86
    @37
    @49
    cR
    cU
    wph
    cU
    cR
    wer
    @85
    eropr.4
    adantr
    @86
    cA
    cU
    @37
    wph
    cA
    cU
    wss
    @85
    eropr.7
    adantr
    wph
    @78
    @79
    @84
    simprll
    #
    sseldd
    erth
    @86
    @40
    @52
    cS
    cV
    wph
    cV
    cS
    wer
    @85
    eropr.5
    adantr
    @86
    cB
    cV
    @40
    wph
    cB
    cV
    wss
    @85
    eropr.8
    adantr
    wph
    @80
    @82
    @83
    simprrl
    #
    sseldd
    erth
    anbi12d
    @86
    @44
    @56
    cT
    cW
    wph
    cW
    cT
    wer
    @85
    eropr.6
    adantr
    @86
    cC
    cW
    @44
    wph
    cC
    cW
    wss
    @85
    eropr.9
    adantr
    @86
    @37
    @40
    cC
    cA
    cB
    c.pl
    wph
    cA
    cB
    cxp
    cC
    c.pl
    wf
    @85
    eropr.10
    adantr
    @95
    @96
    fovrnd
    sseldd
    erth
    3imtr3d
    @58
    @91
    @92
    @19
    @57
    @45
    eqeq2
    biimprcd
    syl6
    impd
    @47
    @59
    @90
    @24
    @91
    @43
    @59
    @90
    wb
    @46
    @43
    @55
    @89
    @58
    @39
    @51
    @87
    @42
    @54
    @88
    cX
    @38
    @50
    eqeq1
    cY
    @41
    @53
    eqeq1
    bi2anan9
    anbi1d
    adantr
    @46
    @24
    @91
    wb
    @43
    @11
    @45
    @19
    eqeq1
    adantl
    imbi12d
    syl5ibrcom
    impd
    anassrs
    rexlimdvva
    syl5bir
    rexlimdvva
    syl5bir
    adantr
    alrimivv
    @17
    @22
    vz
    vw
    @24
    @15
    @21
    vp
    vq
    cA
    cB
    @24
    @14
    @20
    @10
    @11
    @19
    @13
    eqeq1
    anbi2d
    2rexbidv
    eu4
    sylanbrc
end
