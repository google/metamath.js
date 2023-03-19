include "clly.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "llytop.mm"
include "adantl.mm"
include "wss.mm"
include "w3a.mm"
include "simplr.mm"
include "adantr.mm"
include "topopn.mm"
include "syl.mm"
include "simpr.mm"
include "llyi.mm"
include "syl3anc.mm"
include "3simpc.mm"
include "reximi.mm"
include "ralrimiva.mm"
include "jca.mm"
include "cpw.mm"
include "cin.mm"
include "simprl.mm"
include "wi.mm"
include "cuni.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "ssralv.mm"
include "simpllr.mm"
include "simplrl.mm"
include "inopn.mm"
include "inss1.mm"
include "vex.mm"
include "elpw2.mm"
include "mpbir.mm"
include "a1i.mm"
include "elind.mm"
include "simplrr.mm"
include "simprrl.mm"
include "wceq.mm"
include "inss2.mm"
include "restabs.mm"
include "elrestr.mm"
include "simprrr.mm"
include "ralrimivva.mm"
include "ad3antrrr.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "raleqbi1dv.mm"
include "rspcv.mm"
include "sylc.mm"
include "oveq2.mm"
include "eqeltrrd.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimdvaa.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "syld.mm"
include "ralrimdva.mm"
include "impr.mm"
include "islly.mm"
include "sylanbrc.mm"
include "impbida.mm"

theorem islly2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let vj: setvar j
  let cJ: class J
  let cX: class X
  let vk: setvar k
  let vs: setvar s
  let vv: setvar v
  let vz: setvar z
  assume restlly.1: |- ( ( ph /\ ( j e. A /\ x e. j ) ) -> ( j |`t x ) e. A )
  assume islly2.2: |- X = U. J

  disjoint j u
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint u x
  disjoint u y
  disjoint A u
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint J j
  disjoint J u
  disjoint J x
  disjoint J y
  disjoint j ph
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint X u
  disjoint X y
  disjoint j k
  disjoint j s
  disjoint j v
  disjoint j z
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint u v
  disjoint u z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint J v
  disjoint J z
  disjoint k ph
  disjoint ph s
  disjoint ph z
  disjoint X z
  assert |- ( ph -> ( J e. Locally A <-> ( J e. Top /\ A. y e. X E. u e. J ( y e. u /\ ( J |`t u ) e. A ) ) ) )

  proof
    wph
    cJ
    cA
    clly
    wcel
    #
    cJ
    ctop
    wcel
    #
    vy
    cv
    #
    vu
    cv
    #
    wcel
    #
    cJ
    @3
    crest
    co
    #
    cA
    wcel
    #
    wa
    #
    vu
    cJ
    wrex
    #
    vy
    cX
    wral
    #
    wa
    #
    wph
    @0
    wa
    #
    @1
    @9
    @0
    @1
    wph
    cA
    cJ
    llytop
    adantl
    #
    @11
    @8
    vy
    cX
    @11
    @2
    cX
    wcel
    #
    wa
    #
    @3
    cX
    wss
    #
    @4
    @6
    w3a
    #
    vu
    cJ
    wrex
    #
    @8
    @14
    @0
    cX
    cJ
    wcel
    #
    @13
    @17
    wph
    @0
    @13
    simplr
    @14
    @1
    @18
    @11
    @1
    @13
    @12
    adantr
    cJ
    cX
    islly2.2
    topopn
    syl
    @11
    @13
    simpr
    vu
    cA
    @2
    cX
    cJ
    llyi
    syl3anc
    @16
    @7
    vu
    cJ
    @15
    @4
    @6
    3simpc
    reximi
    syl
    ralrimiva
    jca
    wph
    @10
    wa
    @1
    @2
    vv
    cv
    #
    wcel
    #
    cJ
    @19
    crest
    co
    #
    cA
    wcel
    #
    wa
    #
    vv
    cJ
    vz
    cv
    #
    cpw
    #
    cin
    #
    wrex
    #
    vy
    @24
    wral
    #
    vz
    cJ
    wral
    #
    @0
    wph
    @1
    @9
    simprl
    wph
    @1
    @9
    @29
    wph
    @1
    wa
    #
    @9
    @28
    vz
    cJ
    @30
    @24
    cJ
    wcel
    #
    wa
    #
    @9
    @8
    vy
    @24
    wral
    #
    @28
    @32
    @24
    cX
    wss
    #
    @9
    @33
    wi
    @31
    @34
    @30
    @31
    @24
    cJ
    cuni
    cX
    @24
    cJ
    elssuni
    islly2.2
    syl6sseqr
    adantl
    @8
    vy
    @24
    cX
    ssralv
    syl
    @32
    @8
    @27
    vy
    @24
    @30
    @31
    @2
    @24
    wcel
    #
    @8
    @27
    wi
    @30
    @31
    @35
    wa
    #
    wa
    #
    @7
    @27
    vu
    cJ
    @37
    @3
    cJ
    wcel
    #
    @7
    wa
    #
    wa
    #
    @24
    @3
    cin
    #
    @26
    wcel
    @2
    @41
    wcel
    #
    cJ
    @41
    crest
    co
    #
    cA
    wcel
    #
    @27
    @40
    cJ
    @25
    @41
    @40
    @1
    @31
    @38
    @41
    cJ
    wcel
    wph
    @1
    @36
    @39
    simpllr
    #
    @30
    @31
    @35
    @39
    simplrl
    #
    @37
    @38
    @7
    simprl
    #
    @24
    @3
    cJ
    inopn
    syl3anc
    @41
    @25
    wcel
    #
    @40
    @48
    @41
    @24
    wss
    @24
    @3
    inss1
    @41
    @24
    vz
    vex
    elpw2
    mpbir
    a1i
    elind
    @40
    @24
    @3
    @2
    @30
    @31
    @35
    @39
    simplrr
    @37
    @38
    @4
    @6
    simprrl
    elind
    @40
    @5
    @41
    crest
    co
    #
    @43
    cA
    @40
    @1
    @41
    @3
    wss
    #
    @38
    @49
    @43
    wceq
    @45
    @50
    @40
    @24
    @3
    inss2
    a1i
    @47
    @41
    @3
    cJ
    ctop
    cJ
    restabs
    syl3anc
    @40
    @41
    @5
    wcel
    #
    @5
    vx
    cv
    #
    crest
    co
    #
    cA
    wcel
    #
    vx
    @5
    wral
    #
    @49
    cA
    wcel
    #
    @40
    @1
    @38
    @31
    @51
    @45
    @47
    @46
    @24
    @3
    cJ
    ctop
    cJ
    elrestr
    syl3anc
    @40
    @6
    vj
    cv
    #
    @52
    crest
    co
    #
    cA
    wcel
    #
    vx
    @57
    wral
    #
    vj
    cA
    wral
    #
    @55
    @37
    @38
    @4
    @6
    simprrr
    wph
    @61
    @1
    @36
    @39
    wph
    @59
    vj
    vx
    cA
    @57
    restlly.1
    ralrimivva
    ad3antrrr
    @60
    @55
    vj
    @5
    cA
    @59
    @54
    vx
    @57
    @5
    @57
    @5
    wceq
    @58
    @53
    cA
    @57
    @5
    @52
    crest
    oveq1
    eleq1d
    raleqbi1dv
    rspcv
    sylc
    @54
    @56
    vx
    @41
    @5
    @52
    @41
    wceq
    @53
    @49
    cA
    @52
    @41
    @5
    crest
    oveq2
    eleq1d
    rspcv
    sylc
    eqeltrrd
    @23
    @42
    @44
    wa
    vv
    @41
    @26
    @19
    @41
    wceq
    #
    @20
    @42
    @22
    @44
    @19
    @41
    @2
    eleq2
    @62
    @21
    @43
    cA
    @19
    @41
    cJ
    crest
    oveq2
    eleq1d
    anbi12d
    rspcev
    syl12anc
    rexlimdvaa
    anassrs
    ralimdva
    syld
    ralrimdva
    impr
    vz
    vy
    vv
    cA
    cJ
    islly
    sylanbrc
    impbida
end
