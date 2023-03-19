include "cmnd.mm"
include "wcel.mm"
include "cfv.mm"
include "c0g.mm"
include "wceq.mm"
include "cplusg.mm"
include "imasbas.mm"
include "eqidd.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "eqid.mm"
include "3expb.mm"
include "caovclg.mm"
include "imasaddf.mm"
include "fovrn.mm"
include "syl3an1.mm"
include "w3a.mm"
include "wrex.mm"
include "crn.mm"
include "wfo.mm"
include "forn.mm"
include "syl.mm"
include "eleq2d.mm"
include "3anbi123d.mm"
include "wfn.mm"
include "wb.mm"
include "fofn.mm"
include "fvelrnb.mm"
include "bitr3d.mm"
include "3reeanv.mm"
include "syl6bbr.mm"
include "wa.mm"
include "wi.mm"
include "simpl.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "imasaddval.mm"
include "syl3anc.mm"
include "simpr1.mm"
include "3adantr1.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "simp1.mm"
include "simp2.mm"
include "oveq12d.mm"
include "simp3.mm"
include "eqeq12d.mm"
include "syl5ibcom.mm"
include "3exp2.mm"
include "imp32.mm"
include "rexlimdv.mm"
include "rexlimdvva.mm"
include "sylbid.mm"
include "imp.mm"
include "fof.mm"
include "ffvelrnd.mm"
include "adantr.mm"
include "simpr.mm"
include "eqtrd.mm"
include "oveq2.mm"
include "id.mm"
include "rexlimdva.mm"
include "mpd3an3.mm"
include "oveq1.mm"
include "ismndd.mm"
include "grpidd.mm"
include "jca.mm"

theorem imasmnd2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cU: class U
  let cF: class F
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume imasmnd.u: |- ( ph -> U = ( F "s R ) )
  assume imasmnd.v: |- ( ph -> V = ( Base ` R ) )
  assume imasmnd.p: |- .+ = ( +g ` R )
  assume imasmnd.f: |- ( ph -> F : V -onto-> B )
  assume imasmnd.e: |- ( ( ph /\ ( a e. V /\ b e. V ) /\ ( p e. V /\ q e. V ) ) -> ( ( ( F ` a ) = ( F ` p ) /\ ( F ` b ) = ( F ` q ) ) -> ( F ` ( a .+ b ) ) = ( F ` ( p .+ q ) ) ) )
  assume imasmnd2.r: |- ( ph -> R e. W )
  assume imasmnd2.1: |- ( ( ph /\ x e. V /\ y e. V ) -> ( x .+ y ) e. V )
  assume imasmnd2.2: |- ( ( ph /\ ( x e. V /\ y e. V /\ z e. V ) ) -> ( F ` ( ( x .+ y ) .+ z ) ) = ( F ` ( x .+ ( y .+ z ) ) ) )
  assume imasmnd2.3: |- ( ph -> .0. e. V )
  assume imasmnd2.4: |- ( ( ph /\ x e. V ) -> ( F ` ( .0. .+ x ) ) = ( F ` x ) )
  assume imasmnd2.5: |- ( ( ph /\ x e. V ) -> ( F ` ( x .+ .0. ) ) = ( F ` x ) )

  disjoint p q
  disjoint p x
  disjoint p y
  disjoint .+ p
  disjoint q x
  disjoint q y
  disjoint .+ q
  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a ph
  disjoint b p
  disjoint b q
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint b ph
  disjoint p z
  disjoint p ph
  disjoint q z
  disjoint ph q
  disjoint x z
  disjoint ph x
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint U a
  disjoint U b
  disjoint U p
  disjoint U q
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint .0. p
  disjoint .0. q
  disjoint .0. x
  disjoint B p
  disjoint B q
  disjoint F a
  disjoint F b
  disjoint F p
  disjoint F q
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint R p
  disjoint R q
  disjoint V a
  disjoint V b
  disjoint V p
  disjoint V q
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint p u
  disjoint p v
  disjoint p w
  disjoint q u
  disjoint q v
  disjoint q w
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint ph u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint .0. u
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint F u
  assert |- ( ph -> ( U e. Mnd /\ ( F ` .0. ) = ( 0g ` U ) ) )

  proof
    wph
    cU
    cmnd
    wcel
    c.0
    cF
    cfv
    #
    cU
    c0g
    cfv
    wceq
    wph
    vu
    vv
    vw
    cB
    cU
    cplusg
    cfv
    #
    cU
    @0
    wph
    cB
    cR
    cU
    cF
    cV
    cW
    imasmnd.u
    imasmnd.v
    imasmnd.f
    imasmnd2.r
    imasbas
    #
    wph
    @1
    eqidd
    #
    wph
    cB
    cB
    cxp
    cB
    @1
    wf
    vu
    cv
    #
    cB
    wcel
    #
    vv
    cv
    #
    cB
    wcel
    #
    @4
    @6
    @1
    co
    #
    cB
    wcel
    wph
    cB
    cR
    @1
    c.pl
    cU
    cF
    cV
    cW
    vq
    vp
    va
    vb
    imasmnd.f
    imasmnd.e
    imasmnd.u
    imasmnd.v
    imasmnd2.r
    imasmnd.p
    @1
    eqid
    #
    wph
    vx
    vy
    vp
    cv
    vq
    cv
    cV
    cV
    cV
    c.pl
    wph
    vx
    cv
    #
    cV
    wcel
    #
    vy
    cv
    #
    cV
    wcel
    #
    @10
    @12
    c.pl
    co
    #
    cV
    wcel
    #
    imasmnd2.1
    3expb
    caovclg
    #
    imasaddf
    @4
    @6
    cB
    cB
    cB
    @1
    fovrn
    syl3an1
    wph
    @5
    @7
    vw
    cv
    #
    cB
    wcel
    #
    w3a
    #
    @8
    @17
    @1
    co
    #
    @4
    @6
    @17
    @1
    co
    #
    @1
    co
    #
    wceq
    #
    wph
    @19
    @10
    cF
    cfv
    #
    @4
    wceq
    #
    @12
    cF
    cfv
    #
    @6
    wceq
    #
    vz
    cv
    #
    cF
    cfv
    #
    @17
    wceq
    #
    w3a
    #
    vz
    cV
    wrex
    #
    vy
    cV
    wrex
    vx
    cV
    wrex
    #
    @23
    wph
    @19
    @25
    vx
    cV
    wrex
    #
    @27
    vy
    cV
    wrex
    #
    @30
    vz
    cV
    wrex
    #
    w3a
    #
    @33
    wph
    @4
    cF
    crn
    #
    wcel
    #
    @6
    @38
    wcel
    #
    @17
    @38
    wcel
    #
    w3a
    #
    @19
    @37
    wph
    @39
    @5
    @40
    @7
    @41
    @18
    wph
    @38
    cB
    @4
    wph
    cV
    cB
    cF
    wfo
    #
    @38
    cB
    wceq
    imasmnd.f
    cV
    cB
    cF
    forn
    syl
    #
    eleq2d
    #
    wph
    @38
    cB
    @6
    @44
    eleq2d
    wph
    @38
    cB
    @17
    @44
    eleq2d
    3anbi123d
    wph
    cF
    cV
    wfn
    #
    @42
    @37
    wb
    wph
    @43
    @46
    imasmnd.f
    cV
    cB
    cF
    fofn
    syl
    #
    @46
    @39
    @34
    @40
    @35
    @41
    @36
    vx
    cV
    @4
    cF
    fvelrnb
    #
    vy
    cV
    @6
    cF
    fvelrnb
    vz
    cV
    @17
    cF
    fvelrnb
    3anbi123d
    syl
    bitr3d
    @25
    @27
    @30
    vx
    vy
    vz
    cV
    cV
    cV
    3reeanv
    syl6bbr
    wph
    @32
    @23
    vx
    vy
    cV
    cV
    wph
    @11
    @13
    wa
    wa
    @31
    @23
    vz
    cV
    wph
    @11
    @13
    @28
    cV
    wcel
    #
    @31
    @23
    wi
    #
    wi
    wph
    @11
    @13
    @49
    @50
    wph
    @11
    @13
    @49
    w3a
    #
    wa
    #
    @24
    @26
    @1
    co
    #
    @29
    @1
    co
    #
    @24
    @26
    @29
    @1
    co
    #
    @1
    co
    #
    wceq
    @31
    @23
    @52
    @14
    cF
    cfv
    #
    @29
    @1
    co
    #
    @24
    @12
    @28
    c.pl
    co
    #
    cF
    cfv
    #
    @1
    co
    #
    @54
    @56
    @52
    @14
    @28
    c.pl
    co
    cF
    cfv
    #
    @10
    @59
    c.pl
    co
    cF
    cfv
    #
    @58
    @61
    imasmnd2.2
    @52
    wph
    @15
    @49
    @58
    @62
    wceq
    wph
    @51
    simpl
    #
    wph
    @11
    @13
    @15
    @49
    imasmnd2.1
    3adant3r3
    wph
    @11
    @13
    @49
    simpr3
    wph
    cB
    cR
    @1
    c.pl
    cU
    cF
    cV
    @14
    @28
    cW
    vq
    vp
    va
    vb
    imasmnd.f
    imasmnd.e
    imasmnd.u
    imasmnd.v
    imasmnd2.r
    imasmnd.p
    @9
    imasaddval
    syl3anc
    @52
    wph
    @11
    @59
    cV
    wcel
    #
    @61
    @63
    wceq
    @64
    wph
    @11
    @13
    @49
    simpr1
    wph
    @13
    @49
    @65
    @11
    wph
    vp
    vq
    @12
    @28
    cV
    cV
    cV
    c.pl
    @16
    caovclg
    3adantr1
    wph
    cB
    cR
    @1
    c.pl
    cU
    cF
    cV
    @10
    @59
    cW
    vq
    vp
    va
    vb
    imasmnd.f
    imasmnd.e
    imasmnd.u
    imasmnd.v
    imasmnd2.r
    imasmnd.p
    @9
    imasaddval
    syl3anc
    3eqtr4d
    @52
    @53
    @57
    @29
    @1
    wph
    @11
    @13
    @53
    @57
    wceq
    @49
    wph
    cB
    cR
    @1
    c.pl
    cU
    cF
    cV
    @10
    @12
    cW
    vq
    vp
    va
    vb
    imasmnd.f
    imasmnd.e
    imasmnd.u
    imasmnd.v
    imasmnd2.r
    imasmnd.p
    @9
    imasaddval
    3adant3r3
    oveq1d
    @52
    @55
    @60
    @24
    @1
    wph
    @13
    @49
    @55
    @60
    wceq
    @11
    wph
    cB
    cR
    @1
    c.pl
    cU
    cF
    cV
    @12
    @28
    cW
    vq
    vp
    va
    vb
    imasmnd.f
    imasmnd.e
    imasmnd.u
    imasmnd.v
    imasmnd2.r
    imasmnd.p
    @9
    imasaddval
    3adant3r1
    oveq2d
    3eqtr4d
    @31
    @54
    @20
    @56
    @22
    @31
    @53
    @8
    @29
    @17
    @1
    @31
    @24
    @4
    @26
    @6
    @1
    @25
    @27
    @30
    simp1
    #
    @25
    @27
    @30
    simp2
    #
    oveq12d
    @25
    @27
    @30
    simp3
    #
    oveq12d
    @31
    @24
    @4
    @55
    @21
    @1
    @66
    @31
    @26
    @6
    @29
    @17
    @1
    @67
    @68
    oveq12d
    oveq12d
    eqeq12d
    syl5ibcom
    3exp2
    imp32
    rexlimdv
    rexlimdvva
    sylbid
    imp
    wph
    cV
    cB
    c.0
    cF
    wph
    @43
    cV
    cB
    cF
    wf
    imasmnd.f
    cV
    cB
    cF
    fof
    syl
    imasmnd2.3
    ffvelrnd
    #
    wph
    @5
    @0
    @4
    @1
    co
    #
    @4
    wceq
    #
    wph
    @5
    @34
    @71
    wph
    @39
    @5
    @34
    @45
    wph
    @46
    @39
    @34
    wb
    @47
    @48
    syl
    bitr3d
    #
    wph
    @25
    @71
    vx
    cV
    wph
    @11
    wa
    #
    @0
    @24
    @1
    co
    #
    @24
    wceq
    @25
    @71
    @73
    @74
    c.0
    @10
    c.pl
    co
    cF
    cfv
    #
    @24
    @73
    wph
    c.0
    cV
    wcel
    #
    @11
    @74
    @75
    wceq
    wph
    @11
    simpl
    wph
    @76
    @11
    imasmnd2.3
    adantr
    #
    wph
    @11
    simpr
    wph
    cB
    cR
    @1
    c.pl
    cU
    cF
    cV
    c.0
    @10
    cW
    vq
    vp
    va
    vb
    imasmnd.f
    imasmnd.e
    imasmnd.u
    imasmnd.v
    imasmnd2.r
    imasmnd.p
    @9
    imasaddval
    syl3anc
    imasmnd2.4
    eqtrd
    @25
    @74
    @70
    @24
    @4
    @24
    @4
    @0
    @1
    oveq2
    @25
    id
    #
    eqeq12d
    syl5ibcom
    rexlimdva
    sylbid
    imp
    #
    wph
    @5
    @4
    @0
    @1
    co
    #
    @4
    wceq
    #
    wph
    @5
    @34
    @81
    @72
    wph
    @25
    @81
    vx
    cV
    @73
    @24
    @0
    @1
    co
    #
    @24
    wceq
    @25
    @81
    @73
    @82
    @10
    c.0
    c.pl
    co
    cF
    cfv
    #
    @24
    wph
    @11
    @76
    @82
    @83
    wceq
    @77
    wph
    cB
    cR
    @1
    c.pl
    cU
    cF
    cV
    @10
    c.0
    cW
    vq
    vp
    va
    vb
    imasmnd.f
    imasmnd.e
    imasmnd.u
    imasmnd.v
    imasmnd2.r
    imasmnd.p
    @9
    imasaddval
    mpd3an3
    imasmnd2.5
    eqtrd
    @25
    @82
    @80
    @24
    @4
    @24
    @4
    @0
    @1
    oveq1
    @78
    eqeq12d
    syl5ibcom
    rexlimdva
    sylbid
    imp
    #
    ismndd
    wph
    vu
    cB
    @1
    cU
    @0
    @2
    @3
    @69
    @79
    @84
    grpidd
    jca
end
