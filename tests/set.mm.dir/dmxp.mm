include "c0.mm"
include "wne.mm"
include "cxp.mm"
include "cdm.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "df-xp.mm"
include "dmeqi.mm"
include "wex.mm"
include "wral.mm"
include "wceq.mm"
include "n0.mm"
include "biimpi.mm"
include "ralrimivw.mm"
include "dmopab3.mm"
include "sylib.mm"
include "syl5eq.mm"

theorem dmxp
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( B =/= (/) -> dom ( A X. B ) = A )

  proof
    cB
    c0
    wne
    #
    cA
    cB
    cxp
    #
    cdm
    vy
    cv
    cA
    wcel
    vx
    cv
    cB
    wcel
    #
    wa
    vy
    vx
    copab
    #
    cdm
    #
    cA
    @1
    @3
    vy
    vx
    cA
    cB
    df-xp
    dmeqi
    @0
    @2
    vx
    wex
    #
    vy
    cA
    wral
    @4
    cA
    wceq
    @0
    @5
    vy
    cA
    @0
    @5
    vx
    cB
    n0
    biimpi
    ralrimivw
    @2
    vy
    vx
    cA
    dmopab3
    sylib
    syl5eq
end
