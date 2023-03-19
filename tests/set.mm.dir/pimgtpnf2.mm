include "cpnf.mm"
include "cv.mm"
include "cfv.mm"
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
include "breq2d.mm"
include "cbvrab.mm"
include "a1i.mm"
include "wn.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "cr.mm"
include "ffvelrnda.mm"
include "rexrd.mm"
include "cxr.mm"
include "pnfxr.mm"
include "ltpnfd.mm"
include "xrltled.mm"
include "xrlenltd.mm"
include "mpbid.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "eqtrd.mm"

theorem pimgtpnf2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let vk: setvar k
  assume pimgtpnf2.1: |- F/_ x F
  assume pimgtpnf2.2: |- ( ph -> F : A --> RR )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint F y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> { x e. A | +oo < ( F ` x ) } = (/) )

  proof
    wph
    cpnf
    vx
    cv
    #
    cF
    cfv
    #
    clt
    wbr
    #
    vx
    cA
    crab
    #
    cpnf
    vy
    cv
    #
    cF
    cfv
    #
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
    cpnf
    @5
    clt
    vx
    cpnf
    nfcv
    vx
    clt
    nfcv
    vx
    @4
    cF
    pimgtpnf2.1
    vx
    @4
    nfcv
    nffv
    nfbr
    @0
    @4
    wceq
    @1
    @5
    cpnf
    clt
    @0
    @4
    cF
    fveq2
    breq2d
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
    @5
    cpnf
    cle
    wbr
    @8
    @9
    @5
    cpnf
    @9
    @5
    wph
    cA
    cr
    @4
    cF
    pimgtpnf2.2
    ffvelrnda
    #
    rexrd
    #
    cpnf
    cxr
    wcel
    @9
    pnfxr
    a1i
    #
    @9
    @5
    @10
    ltpnfd
    xrltled
    @9
    @5
    cpnf
    @11
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
