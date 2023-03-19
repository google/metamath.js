include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "wa.mm"
include "co.mm"
include "wrex.mm"
include "cio.mm"
include "cmpt2.mm"
include "wcel.mm"
include "wral.mm"
include "cab.mm"
include "wi.mm"
include "cqs.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "fovrnda.mm"
include "ecelqsg.mm"
include "syl2anc.mm"
include "syl6eleqr.mm"
include "eleq1a.mm"
include "syl.mm"
include "adantld.mm"
include "rexlimdvva.mm"
include "abssdv.mm"
include "weu.mm"
include "eroveu.mm"
include "iotacl.mm"
include "sseldd.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "fmpt2.mm"
include "sylib.mm"
include "erovlem.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem eroprf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let c.pd: class .+^
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cJ: class J
  let cK: class K
  let cL: class L
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
  assume eropr.12: |- .+^ = { <. <. x , y >. , z >. | E. p e. A E. q e. B ( ( x = [ p ] R /\ y = [ q ] S ) /\ z = [ ( p .+ q ) ] T ) }
  assume eropr.13: |- ( ph -> R e. X )
  assume eropr.14: |- ( ph -> S e. Y )
  assume eropr.15: |- L = ( C /. T )

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
  disjoint L p
  disjoint L q
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint J p
  disjoint J q
  disjoint J x
  disjoint J y
  disjoint J z
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
  disjoint J w
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
  disjoint K w
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
  disjoint .+ w
  disjoint ph w
  disjoint T w
  disjoint X w
  disjoint Y w
  assert |- ( ph -> .+^ : ( J X. K ) --> L )

  proof
    wph
    cJ
    cK
    cxp
    #
    cL
    c.pd
    wf
    @0
    cL
    vx
    vy
    cJ
    cK
    vx
    cv
    #
    vp
    cv
    #
    cR
    cec
    wceq
    vy
    cv
    #
    vq
    cv
    #
    cS
    cec
    wceq
    wa
    #
    vz
    cv
    #
    @2
    @4
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
    cmpt2
    #
    wf
    #
    wph
    @12
    cL
    wcel
    #
    vy
    cK
    wral
    vx
    cJ
    wral
    @14
    wph
    @15
    vx
    vy
    cJ
    cK
    wph
    @1
    cJ
    wcel
    @3
    cK
    wcel
    wa
    #
    wa
    #
    @11
    vz
    cab
    #
    cL
    @12
    @17
    @11
    vz
    cL
    @17
    @10
    @6
    cL
    wcel
    #
    vp
    vq
    cA
    cB
    @17
    @2
    cA
    wcel
    @4
    cB
    wcel
    wa
    #
    wa
    #
    @9
    @19
    @5
    @21
    @8
    cL
    wcel
    @9
    @19
    wi
    @21
    @8
    cC
    cT
    cqs
    #
    cL
    @21
    cT
    cZ
    wcel
    #
    @7
    cC
    wcel
    @8
    @22
    wcel
    wph
    @23
    @16
    @20
    eropr.3
    ad2antrr
    @17
    @2
    @4
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
    @16
    eropr.10
    adantr
    fovrnda
    cC
    @7
    cT
    cZ
    ecelqsg
    syl2anc
    eropr.15
    syl6eleqr
    @8
    cL
    @6
    eleq1a
    syl
    adantld
    rexlimdvva
    abssdv
    @17
    @11
    vz
    weu
    @12
    @18
    wcel
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
    @1
    @3
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
    @11
    vz
    iotacl
    syl
    sseldd
    ralrimivva
    vx
    vy
    cJ
    cK
    @12
    cL
    @13
    @13
    eqid
    fmpt2
    sylib
    wph
    @0
    cL
    c.pd
    @13
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
    feq1d
    mpbird
end
