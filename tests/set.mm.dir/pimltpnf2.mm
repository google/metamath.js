include "cv.mm"
include "cfv.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "nfcv.mm"
include "nfv.mm"
include "nffv.mm"
include "nfbr.mm"
include "fveq2.mm"
include "breq1d.mm"
include "cbvrab.mm"
include "a1i.mm"
include "cr.mm"
include "ffvelrnda.mm"
include "pimltpnf.mm"
include "eqtrd.mm"

theorem pimltpnf2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let vk: setvar k
  assume pimltpnf2.1: |- F/_ x F
  assume pimltpnf2.2: |- ( ph -> F : A --> RR )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint F y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> { x e. A | ( F ` x ) < +oo } = A )

  proof
    wph
    vx
    cv
    #
    cF
    cfv
    #
    cpnf
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
    cpnf
    clt
    wbr
    #
    vy
    cA
    crab
    #
    cA
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
    cpnf
    clt
    vx
    @4
    cF
    pimltpnf2.1
    vx
    @4
    nfcv
    nffv
    vx
    clt
    nfcv
    vx
    cpnf
    nfcv
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
    breq1d
    cbvrab
    a1i
    wph
    vy
    cA
    @5
    wph
    vy
    nfv
    wph
    cA
    cr
    @4
    cF
    pimltpnf2.2
    ffvelrnda
    pimltpnf
    eqtrd
end
