include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "ctopon.mm"
include "wb.mm"
include "iscnp.mm"
include "syl3anc.mm"
include "ctg.mm"
include "ctb.mm"
include "ctop.mm"
include "topontop.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "tgclb.mm"
include "sylibr.mm"
include "bastg.mm"
include "sseqtr4d.mm"
include "ssralv.mm"
include "anim2d.mm"
include "sylbid.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "tg2.mm"
include "r19.29.mm"
include "sstr.mm"
include "expcom.mm"
include "reximdv.mm"
include "com12.mm"
include "imim2i.mm"
include "imp32.mm"
include "rexlimivw.mm"
include "ex.mm"
include "com23.mm"
include "ralrimdva.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem tgcnp
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vz: setvar z
  assume tgcn.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume tgcn.3: |- ( ph -> K = ( topGen ` B ) )
  assume tgcn.4: |- ( ph -> K e. ( TopOn ` Y ) )
  assume tgcnp.5: |- ( ph -> P e. X )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint P x
  disjoint P y
  disjoint ph x
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint F z
  disjoint J z
  disjoint K z
  disjoint P z
  disjoint ph z
  disjoint X z
  disjoint Y z
  assert |- ( ph -> ( F e. ( ( J CnP K ) ` P ) <-> ( F : X --> Y /\ A. y e. B ( ( F ` P ) e. y -> E. x e. J ( P e. x /\ ( F " x ) C_ y ) ) ) ) )

  proof
    wph
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cP
    cF
    cfv
    #
    vy
    cv
    #
    wcel
    #
    cP
    vx
    cv
    #
    wcel
    #
    cF
    @5
    cima
    #
    @3
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    wi
    #
    vy
    cB
    wral
    #
    wa
    #
    wph
    @0
    @1
    @11
    vy
    cK
    wral
    #
    wa
    #
    @13
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    @0
    @15
    wb
    tgcn.1
    tgcn.4
    tgcnp.5
    vx
    vy
    cP
    cF
    cJ
    cK
    cX
    cY
    iscnp
    syl3anc
    wph
    @14
    @12
    @1
    wph
    cB
    cK
    wss
    @14
    @12
    wi
    wph
    cB
    cB
    ctg
    cfv
    #
    cK
    wph
    cB
    ctb
    wcel
    #
    cB
    @19
    wss
    wph
    @19
    ctop
    wcel
    @20
    wph
    cK
    @19
    ctop
    tgcn.3
    wph
    @17
    cK
    ctop
    wcel
    tgcn.4
    cY
    cK
    topontop
    syl
    eqeltrrd
    cB
    tgclb
    sylibr
    cB
    ctb
    bastg
    syl
    tgcn.3
    sseqtr4d
    @11
    vy
    cB
    cK
    ssralv
    syl
    anim2d
    sylbid
    wph
    @13
    @1
    @2
    vz
    cv
    #
    wcel
    #
    @6
    @7
    @21
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    wi
    #
    vz
    cK
    wral
    #
    wa
    #
    @0
    wph
    @12
    @27
    @1
    wph
    @12
    @26
    vz
    cK
    wph
    @21
    cK
    wcel
    #
    wa
    @21
    @19
    wcel
    #
    @12
    @26
    wi
    wph
    @29
    @30
    wph
    cK
    @19
    @21
    tgcn.3
    eleq2d
    biimpa
    @30
    @22
    @12
    @25
    @30
    @22
    @12
    @25
    wi
    #
    @30
    @22
    wa
    @4
    @3
    @21
    wss
    #
    wa
    #
    vy
    cB
    wrex
    #
    @31
    vy
    @21
    cB
    @2
    tg2
    @12
    @34
    @25
    @12
    @34
    wa
    @11
    @33
    wa
    #
    vy
    cB
    wrex
    @25
    @11
    @33
    vy
    cB
    r19.29
    @35
    @25
    vy
    cB
    @11
    @4
    @32
    @25
    @10
    @32
    @25
    wi
    @4
    @32
    @10
    @25
    @32
    @9
    @24
    vx
    cJ
    @32
    @8
    @23
    @6
    @8
    @32
    @23
    @7
    @3
    @21
    sstr
    expcom
    anim2d
    reximdv
    com12
    imim2i
    imp32
    rexlimivw
    syl
    expcom
    syl
    ex
    com23
    syl
    ralrimdva
    anim2d
    wph
    @16
    @17
    @18
    @0
    @28
    wb
    tgcn.1
    tgcn.4
    tgcnp.5
    vx
    vz
    cP
    cF
    cJ
    cK
    cX
    cY
    iscnp
    syl3anc
    sylibrd
    impbid
end
