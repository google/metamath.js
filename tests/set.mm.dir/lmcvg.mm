include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cdm.mm"
include "wa.mm"
include "cuni.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "clm.mm"
include "wbr.mm"
include "w3a.mm"
include "ctop.mm"
include "ctopon.mm"
include "lmrcl.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "lmbr2.mm"
include "mpbid.mm"
include "simp3d.mm"
include "simpr.mm"
include "ralimi.mm"
include "reximi.mm"
include "imim2i.mm"
include "wceq.mm"
include "eleq2.mm"
include "rexralbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"

theorem lmcvg
  let wph: wff ph
  let cP: class P
  let cU: class U
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cM: class M
  let cZ: class Z
  let vu: setvar u
  assume lmcvg.1: |- Z = ( ZZ>= ` M )
  assume lmcvg.3: |- ( ph -> P e. U )
  assume lmcvg.4: |- ( ph -> M e. ZZ )
  assume lmcvg.5: |- ( ph -> F ( ~~>t ` J ) P )
  assume lmcvg.6: |- ( ph -> U e. J )

  disjoint j k
  disjoint F j
  disjoint F k
  disjoint J j
  disjoint J k
  disjoint P j
  disjoint P k
  disjoint j ph
  disjoint k ph
  disjoint U j
  disjoint U k
  disjoint M j
  disjoint Z j
  disjoint Z k
  disjoint j u
  disjoint k u
  disjoint F u
  disjoint J u
  disjoint P u
  disjoint ph u
  disjoint U u
  disjoint Z u
  assert |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) ( F ` k ) e. U )

  proof
    wph
    cU
    cJ
    wcel
    cP
    vu
    cv
    #
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    @0
    wcel
    #
    vk
    vj
    cv
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    cP
    cU
    wcel
    #
    @3
    cU
    wcel
    #
    vk
    @5
    wral
    vj
    cZ
    wrex
    #
    lmcvg.6
    wph
    @1
    @2
    cF
    cdm
    wcel
    #
    @4
    wa
    #
    vk
    @5
    wral
    #
    vj
    cZ
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    @9
    wph
    cF
    cJ
    cuni
    #
    cc
    cpm
    co
    wcel
    #
    cP
    @19
    wcel
    #
    @18
    wph
    cF
    cP
    cJ
    clm
    cfv
    wbr
    #
    @20
    @21
    @18
    w3a
    lmcvg.5
    wph
    vu
    cP
    vj
    vk
    cF
    cJ
    cM
    @19
    cZ
    wph
    cJ
    ctop
    wcel
    #
    cJ
    @19
    ctopon
    cfv
    wcel
    wph
    @22
    @23
    lmcvg.5
    cP
    cF
    cJ
    lmrcl
    syl
    cJ
    @19
    @19
    eqid
    toptopon
    sylib
    lmcvg.1
    lmcvg.4
    lmbr2
    mpbid
    simp3d
    @17
    @8
    vu
    cJ
    @16
    @7
    @1
    @15
    @6
    vj
    cZ
    @14
    @4
    vk
    @5
    @13
    @4
    simpr
    ralimi
    reximi
    imim2i
    ralimi
    syl
    lmcvg.3
    @8
    @10
    @12
    wi
    vu
    cU
    cJ
    @0
    cU
    wceq
    #
    @1
    @10
    @7
    @12
    @0
    cU
    cP
    eleq2
    @24
    @4
    @11
    vj
    vk
    cZ
    @5
    @0
    cU
    @3
    eleq2
    rexralbidv
    imbi12d
    rspcv
    syl3c
end
