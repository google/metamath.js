include "ccl.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "cdm.mm"
include "wa.mm"
include "cuz.mm"
include "wrex.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "clm.mm"
include "wbr.mm"
include "w3a.mm"
include "lmbr2.mm"
include "mpbid.mm"
include "simp3d.mm"
include "r19.2uz.mm"
include "inelcm.mm"
include "a1i.mm"
include "mpan2d.mm"
include "adantld.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "imim2d.mm"
include "ralimdv.mm"
include "mpd.mm"
include "ctop.mm"
include "cuni.mm"
include "wss.mm"
include "wb.mm"
include "ctopon.mm"
include "topontop.mm"
include "syl.mm"
include "wceq.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "lmcl.mm"
include "syl2anc.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "elcls.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem lmcls
  let wph: wff ph
  let cP: class P
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vj: setvar j
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  assume lmff.1: |- Z = ( ZZ>= ` M )
  assume lmff.3: |- ( ph -> J e. ( TopOn ` X ) )
  assume lmff.4: |- ( ph -> M e. ZZ )
  assume lmcls.5: |- ( ph -> F ( ~~>t ` J ) P )
  assume lmcls.7: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. S )
  assume lmcls.8: |- ( ph -> S C_ X )

  disjoint F k
  disjoint J k
  disjoint M k
  disjoint P k
  disjoint S k
  disjoint k ph
  disjoint X k
  disjoint Z k
  disjoint j k
  disjoint j u
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J j
  disjoint J u
  disjoint J x
  disjoint J y
  disjoint M j
  disjoint P j
  disjoint P u
  disjoint S u
  disjoint j ph
  disjoint ph u
  disjoint ph y
  disjoint X j
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint Z j
  disjoint Z u
  disjoint Z x
  assert |- ( ph -> P e. ( ( cls ` J ) ` S ) )

  proof
    wph
    cP
    cS
    cJ
    ccl
    cfv
    cfv
    wcel
    #
    cP
    vu
    cv
    #
    wcel
    #
    @1
    cS
    cin
    c0
    wne
    #
    wi
    #
    vu
    cJ
    wral
    #
    wph
    @2
    vk
    cv
    #
    cF
    cdm
    wcel
    #
    @6
    cF
    cfv
    #
    @1
    wcel
    #
    wa
    #
    vk
    vj
    cv
    cuz
    cfv
    wral
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
    @5
    wph
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    cP
    cX
    wcel
    #
    @13
    wph
    cF
    cP
    cJ
    clm
    cfv
    wbr
    #
    @14
    @15
    @13
    w3a
    lmcls.5
    wph
    vu
    cP
    vj
    vk
    cF
    cJ
    cM
    cX
    cZ
    lmff.3
    lmff.1
    lmff.4
    lmbr2
    mpbid
    simp3d
    wph
    @12
    @4
    vu
    cJ
    wph
    @11
    @3
    @2
    @11
    @10
    vk
    cZ
    wrex
    wph
    @3
    @10
    vj
    vk
    cM
    cZ
    lmff.1
    r19.2uz
    wph
    @10
    @3
    vk
    cZ
    wph
    @6
    cZ
    wcel
    wa
    #
    @9
    @3
    @7
    @17
    @9
    @8
    cS
    wcel
    #
    @3
    lmcls.7
    @9
    @18
    wa
    @3
    wi
    @17
    @8
    @1
    cS
    inelcm
    a1i
    mpan2d
    adantld
    rexlimdva
    syl5
    imim2d
    ralimdv
    mpd
    wph
    cJ
    ctop
    wcel
    #
    cS
    cJ
    cuni
    #
    wss
    cP
    @20
    wcel
    @0
    @5
    wb
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @19
    lmff.3
    cX
    cJ
    topontop
    syl
    wph
    cS
    cX
    @20
    lmcls.8
    wph
    @21
    cX
    @20
    wceq
    lmff.3
    cX
    cJ
    toponuni
    syl
    #
    sseqtrd
    wph
    cP
    cX
    @20
    wph
    @21
    @16
    @15
    lmff.3
    lmcls.5
    cP
    cF
    cJ
    cX
    lmcl
    syl2anc
    @22
    eleqtrd
    vu
    cP
    cS
    cJ
    @20
    @20
    eqid
    elcls
    syl3anc
    mpbird
end
