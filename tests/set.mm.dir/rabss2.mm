include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "wi.mm"
include "wal.mm"
include "pm3.45.mm"
include "alimi.mm"
include "dfss2.mm"
include "ss2ab.mm"
include "3imtr4i.mm"
include "df-rab.mm"
include "3sstr4g.mm"

theorem rabss2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A C_ B -> { x e. A | ph } C_ { x e. B | ph } )

  proof
    cA
    cB
    wss
    #
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    @1
    cB
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    wph
    vx
    cA
    crab
    wph
    vx
    cB
    crab
    @2
    @5
    wi
    #
    vx
    wal
    @3
    @6
    wi
    #
    vx
    wal
    @0
    @4
    @7
    wss
    @8
    @9
    vx
    @2
    @5
    wph
    pm3.45
    alimi
    vx
    cA
    cB
    dfss2
    @3
    @6
    vx
    ss2ab
    3imtr4i
    wph
    vx
    cA
    df-rab
    wph
    vx
    cB
    df-rab
    3sstr4g
end
