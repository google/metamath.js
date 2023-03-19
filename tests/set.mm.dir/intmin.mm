include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "wi.mm"
include "wral.mm"
include "vex.mm"
include "elintrab.mm"
include "ssid.mm"
include "wceq.mm"
include "sseq2.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "mpii.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "ssintub.mm"
include "a1i.mm"
include "eqssd.mm"

theorem intmin
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let wph: wff ph

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint ph y
  assert |- ( A e. B -> |^| { x e. B | A C_ x } = A )

  proof
    cA
    cB
    wcel
    #
    cA
    vx
    cv
    #
    wss
    #
    vx
    cB
    crab
    cint
    #
    cA
    @0
    vy
    @3
    cA
    vy
    cv
    #
    @3
    wcel
    @2
    @4
    @1
    wcel
    #
    wi
    #
    vx
    cB
    wral
    #
    @0
    @4
    cA
    wcel
    #
    @2
    vx
    @4
    cB
    vy
    vex
    elintrab
    @0
    @7
    cA
    cA
    wss
    #
    @8
    cA
    ssid
    @6
    @9
    @8
    wi
    vx
    cA
    cB
    @1
    cA
    wceq
    @2
    @9
    @5
    @8
    @1
    cA
    cA
    sseq2
    @1
    cA
    @4
    eleq2
    imbi12d
    rspcv
    mpii
    syl5bi
    ssrdv
    cA
    @3
    wss
    @0
    vx
    cA
    cB
    ssintub
    a1i
    eqssd
end
