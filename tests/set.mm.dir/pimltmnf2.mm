include "cv.mm"
include "cfv.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "c0.mm"
include "wceq.mm"
include "nfcv.mm"
include "nfv.mm"
include "nffv.mm"
include "nfbr.mm"
include "fveq2.mm"
include "breq1d.mm"
include "cbvrab.mm"
include "a1i.mm"
include "wn.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "cxr.mm"
include "mnfxr.mm"
include "cr.mm"
include "ffvelrnda.mm"
include "rexrd.mm"
include "mnfltd.mm"
include "xrltled.mm"
include "xrlenltd.mm"
include "mpbid.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "eqtrd.mm"

theorem pimltmnf2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let vk: setvar k
  assume pimltmnf2.1: |- F/_ x F
  assume pimltmnf2.2: |- ( ph -> F : A --> RR )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint F y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> { x e. A | ( F ` x ) < -oo } = (/) )

  proof
    wph
    vx
    cv
    #
    cF
    cfv
    #
    cmnf
    clt
    wbr
    #
    vx
    cA
    crab
    #
    vy
    cv
    #
    cF
    cfv
    #
    cmnf
    clt
    wbr
    #
    vy
    cA
    crab
    #
    c0
    @3
    @7
    wceq
    wph
    @2
    @6
    vx
    vy
    cA
    vx
    cA
    nfcv
    vy
    cA
    nfcv
    @2
    vy
    nfv
    vx
    @5
    cmnf
    clt
    vx
    @4
    cF
    pimltmnf2.1
    vx
    @4
    nfcv
    nffv
    vx
    clt
    nfcv
    vx
    cmnf
    nfcv
    nfbr
    @0
    @4
    wceq
    @1
    @5
    cmnf
    clt
    @0
    @4
    cF
    fveq2
    breq1d
    cbvrab
    a1i
    wph
    @6
    wn
    #
    vy
    cA
    wral
    @7
    c0
    wceq
    wph
    @8
    vy
    cA
    wph
    @4
    cA
    wcel
    wa
    #
    cmnf
    @5
    cle
    wbr
    @8
    @9
    cmnf
    @5
    cmnf
    cxr
    wcel
    @9
    mnfxr
    a1i
    #
    @9
    @5
    wph
    cA
    cr
    @4
    cF
    pimltmnf2.2
    ffvelrnda
    #
    rexrd
    #
    @9
    @5
    @11
    mnfltd
    xrltled
    @9
    cmnf
    @5
    @10
    @12
    xrlenltd
    mpbid
    ralrimiva
    @6
    vy
    cA
    rabeq0
    sylibr
    eqtrd
end
