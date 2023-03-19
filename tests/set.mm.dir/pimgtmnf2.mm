include "cmnf.mm"
include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "wss.mm"
include "ssrab2.mm"
include "a1i.mm"
include "wral.mm"
include "wa.mm"
include "ssid.mm"
include "wcel.mm"
include "cr.mm"
include "ffvelrnda.mm"
include "mnfltd.mm"
include "ralrimiva.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfv.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "cbvral.mm"
include "sylib.mm"
include "jca.mm"
include "ssrabf.mm"
include "sylibr.mm"
include "eqssd.mm"

theorem pimgtmnf2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let vk: setvar k
  assume pimgtmnf2.1: |- F/_ x F
  assume pimgtmnf2.2: |- ( ph -> F : A --> RR )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint F y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> { x e. A | -oo < ( F ` x ) } = A )

  proof
    wph
    cmnf
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
    cA
    @3
    cA
    wss
    wph
    @2
    vx
    cA
    ssrab2
    a1i
    wph
    cA
    cA
    wss
    #
    @2
    vx
    cA
    wral
    #
    wa
    cA
    @3
    wss
    wph
    @4
    @5
    @4
    wph
    cA
    ssid
    a1i
    wph
    cmnf
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
    wral
    @5
    wph
    @8
    vy
    cA
    wph
    @6
    cA
    wcel
    wa
    @7
    wph
    cA
    cr
    @6
    cF
    pimgtmnf2.2
    ffvelrnda
    mnfltd
    ralrimiva
    @8
    @2
    vy
    vx
    cA
    vx
    cmnf
    @7
    clt
    vx
    cmnf
    nfcv
    vx
    clt
    nfcv
    vx
    @6
    cF
    pimgtmnf2.1
    vx
    @6
    nfcv
    nffv
    nfbr
    @2
    vy
    nfv
    @6
    @0
    wceq
    @7
    @1
    cmnf
    clt
    @6
    @0
    cF
    fveq2
    breq2d
    cbvral
    sylib
    jca
    @2
    vx
    cA
    cA
    vx
    cA
    nfcv
    #
    @9
    ssrabf
    sylibr
    eqssd
end
