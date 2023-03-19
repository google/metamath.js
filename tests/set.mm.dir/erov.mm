include "wcel.mm"
include "w3a.mm"
include "cec.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cio.mm"
include "cvv.mm"
include "cmpt2.mm"
include "erovlem.mm"
include "3ad2ant1.mm"
include "simprl.mm"
include "eqeq1d.mm"
include "simprr.mm"
include "anbi12d.mm"
include "anbi1d.mm"
include "2rexbidv.mm"
include "iotabidv.mm"
include "cqs.mm"
include "ecelqsg.mm"
include "syl6eleqr.mm"
include "sylan.mm"
include "3adant3.mm"
include "3adant2.mm"
include "iotaex.mm"
include "a1i.mm"
include "ovmpt2d.mm"
include "eqid.mm"
include "pm3.2i.mm"
include "eceq1.mm"
include "eqeq2d.mm"
include "oveq1.mm"
include "eceq1d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "mp3an3.mm"
include "3adant1.mm"
include "ecexg.mm"
include "syl.mm"
include "weu.mm"
include "simp1.mm"
include "eroveu.mm"
include "syl12anc.mm"
include "simpr.mm"
include "iota2d.mm"
include "mpbid.mm"
include "eqtrd.mm"

theorem erov
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.pl: class .+
  let c.pd: class .+^
  let cQ: class Q
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
  let cL: class L
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
  assume eropr.12: |- .+^ = { <. <. x , y >. , z >. | E. p e. A E. q e. B ( ( x = [ p ] R /\ y = [ q ] S ) /\ z = [ ( p .+ q ) ] T ) }
  assume eropr.13: |- ( ph -> R e. X )
  assume eropr.14: |- ( ph -> S e. Y )

  disjoint p q
  disjoint p r
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint A p
  disjoint q r
  disjoint q s
  disjoint q t
  disjoint q u
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s t
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B p
  disjoint B q
  disjoint B r
  disjoint B s
  disjoint B t
  disjoint B u
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint J p
  disjoint J q
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint P p
  disjoint P q
  disjoint P r
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint R p
  disjoint R q
  disjoint R r
  disjoint R s
  disjoint R t
  disjoint R u
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint K p
  disjoint K q
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint Q p
  disjoint Q q
  disjoint Q r
  disjoint Q s
  disjoint Q t
  disjoint Q u
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint S p
  disjoint S q
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint .+ p
  disjoint .+ q
  disjoint .+ r
  disjoint .+ s
  disjoint .+ t
  disjoint .+ u
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint p ph
  disjoint ph q
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint T p
  disjoint T q
  disjoint T r
  disjoint T s
  disjoint T t
  disjoint T u
  disjoint T x
  disjoint T y
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
  disjoint q w
  disjoint r w
  disjoint s w
  disjoint t w
  disjoint u w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint L p
  disjoint L q
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint J w
  disjoint R w
  disjoint K w
  disjoint S w
  disjoint .+ w
  disjoint ph w
  disjoint T w
  disjoint X w
  disjoint Y w
  assert |- ( ( ph /\ P e. A /\ Q e. B ) -> ( [ P ] R .+^ [ Q ] S ) = [ ( P .+ Q ) ] T )

  proof
    wph
    cP
    cA
    wcel
    #
    cQ
    cB
    wcel
    #
    w3a
    #
    cP
    cR
    cec
    #
    cQ
    cS
    cec
    #
    c.pd
    co
    @3
    vp
    cv
    #
    cR
    cec
    #
    wceq
    #
    @4
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
    @5
    @8
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
    vp
    cA
    wrex
    #
    vz
    cio
    #
    cP
    cQ
    c.pl
    co
    #
    cT
    cec
    #
    @2
    vx
    vy
    @3
    @4
    cJ
    cK
    vx
    cv
    #
    @6
    wceq
    #
    vy
    cv
    #
    @9
    wceq
    #
    wa
    #
    @15
    wa
    #
    vq
    cB
    wrex
    vp
    cA
    wrex
    #
    vz
    cio
    #
    @18
    c.pd
    cvv
    wph
    @0
    c.pd
    vx
    vy
    cJ
    cK
    @28
    cmpt2
    wceq
    @1
    wph
    vx
    vy
    vz
    vu
    vt
    cA
    cB
    cC
    c.pl
    c.pd
    cR
    cS
    cT
    cU
    cJ
    cK
    cV
    cW
    cZ
    vs
    vr
    vq
    vp
    eropr.1
    eropr.2
    eropr.3
    eropr.4
    eropr.5
    eropr.6
    eropr.7
    eropr.8
    eropr.9
    eropr.10
    eropr.11
    eropr.12
    erovlem
    3ad2ant1
    @2
    @21
    @3
    wceq
    #
    @23
    @4
    wceq
    #
    wa
    wa
    #
    @27
    @17
    vz
    @31
    @26
    @16
    vp
    vq
    cA
    cB
    @31
    @25
    @11
    @15
    @31
    @22
    @7
    @24
    @10
    @31
    @21
    @3
    @6
    @2
    @29
    @30
    simprl
    eqeq1d
    @31
    @23
    @4
    @9
    @2
    @29
    @30
    simprr
    eqeq1d
    anbi12d
    anbi1d
    2rexbidv
    iotabidv
    wph
    @0
    @3
    cJ
    wcel
    #
    @1
    wph
    cR
    cX
    wcel
    #
    @0
    @32
    eropr.13
    @33
    @0
    wa
    @3
    cA
    cR
    cqs
    cJ
    cA
    cP
    cR
    cX
    ecelqsg
    eropr.1
    syl6eleqr
    sylan
    3adant3
    #
    wph
    @1
    @4
    cK
    wcel
    #
    @0
    wph
    cS
    cY
    wcel
    #
    @1
    @35
    eropr.14
    @36
    @1
    wa
    @4
    cB
    cS
    cqs
    cK
    cB
    cQ
    cS
    cY
    ecelqsg
    eropr.2
    syl6eleqr
    sylan
    3adant2
    #
    @18
    cvv
    wcel
    @2
    @17
    vz
    iotaex
    a1i
    ovmpt2d
    @2
    @11
    @20
    @14
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
    @18
    @20
    wceq
    @0
    @1
    @40
    wph
    @0
    @1
    @3
    @3
    wceq
    #
    @4
    @4
    wceq
    #
    wa
    #
    @20
    @20
    wceq
    #
    wa
    #
    @40
    @43
    @44
    @41
    @42
    @3
    eqid
    @4
    eqid
    pm3.2i
    @20
    eqid
    pm3.2i
    @39
    @45
    @41
    @10
    wa
    #
    @20
    cP
    @8
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
    cP
    cQ
    cA
    cB
    @5
    cP
    wceq
    #
    @11
    @46
    @38
    @49
    @50
    @7
    @41
    @10
    @50
    @6
    @3
    @3
    @5
    cP
    cR
    eceq1
    eqeq2d
    anbi1d
    @50
    @14
    @48
    @20
    @50
    @13
    @47
    cT
    @5
    cP
    @8
    c.pl
    oveq1
    eceq1d
    eqeq2d
    anbi12d
    @8
    cQ
    wceq
    #
    @46
    @43
    @49
    @44
    @51
    @10
    @42
    @41
    @51
    @9
    @4
    @4
    @8
    cQ
    cS
    eceq1
    eqeq2d
    anbi2d
    @51
    @48
    @20
    @20
    @51
    @47
    @19
    cT
    @8
    cQ
    cP
    c.pl
    oveq2
    eceq1d
    eqeq2d
    anbi12d
    rspc2ev
    mp3an3
    3adant1
    @2
    @17
    @40
    vz
    @20
    cvv
    wph
    @0
    @20
    cvv
    wcel
    #
    @1
    wph
    cT
    cZ
    wcel
    @52
    eropr.3
    @19
    cZ
    cT
    ecexg
    syl
    3ad2ant1
    @2
    wph
    @32
    @35
    @17
    vz
    weu
    wph
    @0
    @1
    simp1
    @34
    @37
    wph
    vz
    vu
    vt
    cA
    cB
    cC
    c.pl
    cR
    cS
    cT
    cU
    cJ
    cK
    cV
    cW
    @3
    @4
    cZ
    vs
    vr
    vq
    vp
    eropr.1
    eropr.2
    eropr.3
    eropr.4
    eropr.5
    eropr.6
    eropr.7
    eropr.8
    eropr.9
    eropr.10
    eropr.11
    eroveu
    syl12anc
    @2
    @12
    @20
    wceq
    #
    wa
    #
    @16
    @39
    vp
    vq
    cA
    cB
    @54
    @15
    @38
    @11
    @54
    @12
    @20
    @14
    @2
    @53
    simpr
    eqeq1d
    anbi2d
    2rexbidv
    iota2d
    mpbid
    eqtrd
end
