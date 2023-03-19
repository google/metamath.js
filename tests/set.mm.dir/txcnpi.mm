include "cop.mm"
include "cv.mm"
include "wcel.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "wrex.mm"
include "cxp.mm"
include "ccnv.mm"
include "w3a.mm"
include "ccnp.mm"
include "cfv.mm"
include "df-ov.mm"
include "syl5eqelr.mm"
include "cnpimaex.mm"
include "syl3anc.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "cuni.mm"
include "wf.mm"
include "eqid.mm"
include "cnpf.mm"
include "syl.mm"
include "adantr.mm"
include "ffun.mm"
include "elssuni.mm"
include "wceq.mm"
include "fdm.mm"
include "sseq2d.mm"
include "biimpar.mm"
include "sylan2.mm"
include "funimass3.mm"
include "syl2anc.mm"
include "anbi2d.mm"
include "wral.mm"
include "wi.mm"
include "ctopon.mm"
include "eltx.mm"
include "biimpa.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "2rexbidv.mm"
include "rspccv.mm"
include "sstr2.mm"
include "com12.mm"
include "anim2d.mm"
include "opelxp.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "3imtr4g.mm"
include "reximdv.mm"
include "syl6.mm"
include "impd.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem txcnpi
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cU: class U
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vz: setvar z
  assume txcnpi.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume txcnpi.2: |- ( ph -> K e. ( TopOn ` Y ) )
  assume txcnpi.3: |- ( ph -> F e. ( ( ( J tX K ) CnP L ) ` <. A , B >. ) )
  assume txcnpi.4: |- ( ph -> U e. L )
  assume txcnpi.5: |- ( ph -> A e. X )
  assume txcnpi.6: |- ( ph -> B e. Y )
  assume txcnpi.7: |- ( ph -> ( A F B ) e. U )

  disjoint u v
  disjoint A u
  disjoint A v
  disjoint B u
  disjoint B v
  disjoint F u
  disjoint F v
  disjoint J u
  disjoint J v
  disjoint K u
  disjoint K v
  disjoint U u
  disjoint U v
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v z
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint B w
  disjoint B z
  disjoint F w
  disjoint J w
  disjoint J z
  disjoint L w
  disjoint K w
  disjoint K z
  disjoint ph w
  disjoint U w
  assert |- ( ph -> E. u e. J E. v e. K ( A e. u /\ B e. v /\ ( u X. v ) C_ ( `' F " U ) ) )

  proof
    wph
    cA
    cB
    cop
    #
    vw
    cv
    #
    wcel
    #
    cF
    @1
    cima
    cU
    wss
    #
    wa
    #
    vw
    cJ
    cK
    ctx
    co
    #
    wrex
    #
    cA
    vu
    cv
    #
    wcel
    #
    cB
    vv
    cv
    #
    wcel
    #
    @7
    @9
    cxp
    #
    cF
    ccnv
    cU
    cima
    #
    wss
    #
    w3a
    #
    vv
    cK
    wrex
    #
    vu
    cJ
    wrex
    #
    wph
    cF
    @0
    @5
    cL
    ccnp
    co
    cfv
    wcel
    #
    cU
    cL
    wcel
    @0
    cF
    cfv
    #
    cU
    wcel
    @6
    txcnpi.3
    txcnpi.4
    wph
    @18
    cA
    cB
    cF
    co
    cU
    cA
    cB
    cF
    df-ov
    txcnpi.7
    syl5eqelr
    vw
    cU
    @0
    cF
    @5
    cL
    cnpimaex
    syl3anc
    wph
    @4
    @16
    vw
    @5
    wph
    @1
    @5
    wcel
    #
    wa
    #
    @4
    @2
    @1
    @12
    wss
    #
    wa
    #
    @16
    @20
    @3
    @21
    @2
    @20
    cF
    wfun
    #
    @1
    cF
    cdm
    #
    wss
    #
    @3
    @21
    wb
    @20
    @5
    cuni
    #
    cL
    cuni
    #
    cF
    wf
    #
    @23
    wph
    @28
    @19
    wph
    @17
    @28
    txcnpi.3
    @0
    cF
    @5
    cL
    @26
    @27
    @26
    eqid
    @27
    eqid
    cnpf
    syl
    #
    adantr
    @26
    @27
    cF
    ffun
    syl
    @19
    wph
    @1
    @26
    wss
    #
    @25
    @1
    @5
    elssuni
    wph
    @25
    @30
    wph
    @24
    @26
    @1
    wph
    @28
    @24
    @26
    wceq
    @29
    @26
    @27
    cF
    fdm
    syl
    sseq2d
    biimpar
    sylan2
    @1
    cU
    cF
    funimass3
    syl2anc
    anbi2d
    @20
    vz
    cv
    #
    @11
    wcel
    #
    @11
    @1
    wss
    #
    wa
    #
    vv
    cK
    wrex
    vu
    cJ
    wrex
    #
    vz
    @1
    wral
    #
    @22
    @16
    wi
    wph
    @19
    @36
    wph
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    cK
    cY
    ctopon
    cfv
    #
    wcel
    @19
    @36
    wb
    txcnpi.1
    txcnpi.2
    vu
    vv
    @1
    cJ
    cK
    @37
    @38
    vz
    eltx
    syl2anc
    biimpa
    @36
    @2
    @21
    @16
    @36
    @2
    @0
    @11
    wcel
    #
    @33
    wa
    #
    vv
    cK
    wrex
    #
    vu
    cJ
    wrex
    #
    @21
    @16
    wi
    @35
    @42
    vz
    @0
    @1
    @31
    @0
    wceq
    #
    @34
    @40
    vu
    vv
    cJ
    cK
    @43
    @32
    @39
    @33
    @31
    @0
    @11
    eleq1
    anbi1d
    2rexbidv
    rspccv
    @21
    @42
    @16
    @21
    @41
    @15
    vu
    cJ
    @21
    @40
    @14
    vv
    cK
    @21
    @8
    @10
    wa
    #
    @33
    wa
    @44
    @13
    wa
    @40
    @14
    @21
    @33
    @13
    @44
    @33
    @21
    @13
    @11
    @1
    @12
    sstr2
    com12
    anim2d
    @39
    @44
    @33
    cA
    cB
    @7
    @9
    opelxp
    anbi1i
    @8
    @10
    @13
    df-3an
    3imtr4g
    reximdv
    reximdv
    com12
    syl6
    impd
    syl
    sylbid
    rexlimdva
    mpd
end
