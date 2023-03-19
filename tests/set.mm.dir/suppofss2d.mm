include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cof.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "csupp.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofval.mm"
include "adantr.mm"
include "simpr.mm"
include "oveq2d.mm"
include "ralrimiva.mm"
include "ffvelrnda.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "rspcdv.mm"
include "mpd.mm"
include "3eqtrd.mm"
include "ex.mm"
include "offn.mm"
include "ssid.mm"
include "a1i.mm"
include "suppfnss.mm"
include "syl23anc.mm"

theorem suppofss2d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let cZ: class Z
  let vy: setvar y
  assume suppofssd.1: |- ( ph -> A e. V )
  assume suppofssd.2: |- ( ph -> Z e. B )
  assume suppofssd.3: |- ( ph -> F : A --> B )
  assume suppofssd.4: |- ( ph -> G : A --> B )
  assume suppofss2d.5: |- ( ( ph /\ x e. B ) -> ( x X Z ) = Z )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint G x
  disjoint X x
  disjoint Z x
  disjoint ph x
  disjoint A y
  disjoint x y
  disjoint F y
  disjoint G y
  disjoint X y
  disjoint Z y
  disjoint ph y
  assert |- ( ph -> ( ( F oF X G ) supp Z ) C_ ( G supp Z ) )

  proof
    wph
    vy
    cv
    #
    cG
    cfv
    #
    cZ
    wceq
    #
    @0
    cF
    cG
    cX
    cof
    co
    #
    cfv
    #
    cZ
    wceq
    #
    wi
    #
    vy
    cA
    wral
    #
    @3
    cZ
    csupp
    co
    cG
    cZ
    csupp
    co
    wss
    #
    wph
    @6
    vy
    cA
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @2
    @5
    @10
    @2
    wa
    #
    @4
    @0
    cF
    cfv
    #
    @1
    cX
    co
    #
    @12
    cZ
    cX
    co
    #
    cZ
    @10
    @4
    @13
    wceq
    @2
    wph
    cA
    cA
    @12
    @1
    cX
    cA
    cF
    cG
    cV
    cV
    @0
    wph
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    suppofssd.3
    cA
    cB
    cF
    ffn
    syl
    #
    wph
    cA
    cB
    cG
    wf
    cG
    cA
    wfn
    #
    suppofssd.4
    cA
    cB
    cG
    ffn
    syl
    #
    suppofssd.1
    suppofssd.1
    cA
    inidm
    #
    @10
    @12
    eqidd
    @10
    @1
    eqidd
    ofval
    adantr
    @11
    @1
    cZ
    @12
    cX
    @10
    @2
    simpr
    oveq2d
    @10
    @14
    cZ
    wceq
    #
    @2
    @10
    vx
    cv
    #
    cZ
    cX
    co
    #
    cZ
    wceq
    #
    vx
    cB
    wral
    #
    @19
    wph
    @23
    @9
    wph
    @22
    vx
    cB
    suppofss2d.5
    ralrimiva
    adantr
    @10
    @22
    @19
    vx
    @12
    cB
    wph
    cA
    cB
    @0
    cF
    suppofssd.3
    ffvelrnda
    @10
    @20
    @12
    wceq
    #
    wa
    #
    @21
    @14
    cZ
    @25
    @20
    @12
    cZ
    cX
    @10
    @24
    simpr
    oveq1d
    eqeq1d
    rspcdv
    mpd
    adantr
    3eqtrd
    ex
    ralrimiva
    wph
    @3
    cA
    wfn
    @16
    cA
    cA
    wss
    #
    cA
    cV
    wcel
    cZ
    cB
    wcel
    @7
    @8
    wi
    wph
    cA
    cA
    cX
    cA
    cF
    cG
    cV
    cV
    @15
    @17
    suppofssd.1
    suppofssd.1
    @18
    offn
    @17
    @26
    wph
    cA
    ssid
    a1i
    suppofssd.1
    suppofssd.2
    vy
    cA
    cA
    @3
    cG
    cV
    cB
    cZ
    suppfnss
    syl23anc
    mpd
end
