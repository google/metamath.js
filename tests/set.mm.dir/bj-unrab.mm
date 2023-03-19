include "crab.mm"
include "wo.mm"
include "cun.mm"
include "wss.mm"
include "ssun1.mm"
include "rabss2.mm"
include "ax-mp.mm"
include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "orc.mm"
include "a1i.mm"
include "ss2rabi.mm"
include "sstri.mm"
include "ssun2.mm"
include "olc.mm"
include "unssi.mm"

theorem bj-unrab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( { x e. A | ph } u. { x e. B | ps } ) C_ { x e. ( A u. B ) | ( ph \/ ps ) }

  proof
    wph
    vx
    cA
    crab
    #
    wps
    vx
    cB
    crab
    #
    wph
    wps
    wo
    #
    vx
    cA
    cB
    cun
    #
    crab
    #
    @0
    wph
    vx
    @3
    crab
    #
    @4
    cA
    @3
    wss
    @0
    @5
    wss
    cA
    cB
    ssun1
    wph
    vx
    cA
    @3
    rabss2
    ax-mp
    wph
    @2
    vx
    @3
    wph
    @2
    wi
    vx
    cv
    @3
    wcel
    #
    wph
    wps
    orc
    a1i
    ss2rabi
    sstri
    @1
    wps
    vx
    @3
    crab
    #
    @4
    cB
    @3
    wss
    @1
    @7
    wss
    cB
    cA
    ssun2
    wps
    vx
    cB
    @3
    rabss2
    ax-mp
    wps
    @2
    vx
    @3
    wps
    @2
    wi
    @6
    wps
    wph
    olc
    a1i
    ss2rabi
    sstri
    unssi
end
