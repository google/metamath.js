include "wss.mm"
include "wpo.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "wa.mm"
include "wor.mm"
include "poss.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "ssel.mm"
include "anim12d.mm"
include "imim1d.mm"
include "2alimdv.mm"
include "r2al.mm"
include "3imtr4g.mm"
include "df-so.mm"

theorem soss
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( A C_ B -> ( R Or B -> R Or A ) )

  proof
    cA
    cB
    wss
    #
    cB
    cR
    wpo
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    vx
    vy
    weq
    @3
    @2
    cR
    wbr
    w3o
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    cA
    cR
    wpo
    #
    @4
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    cB
    cR
    wor
    cA
    cR
    wor
    @0
    @1
    @6
    @5
    @7
    cA
    cB
    cR
    poss
    @0
    @2
    cB
    wcel
    #
    @3
    cB
    wcel
    #
    wa
    #
    @4
    wi
    #
    vy
    wal
    vx
    wal
    @2
    cA
    wcel
    #
    @3
    cA
    wcel
    #
    wa
    #
    @4
    wi
    #
    vy
    wal
    vx
    wal
    @5
    @7
    @0
    @11
    @15
    vx
    vy
    @0
    @14
    @10
    @4
    @0
    @12
    @8
    @13
    @9
    cA
    cB
    @2
    ssel
    cA
    cB
    @3
    ssel
    anim12d
    imim1d
    2alimdv
    @4
    vx
    vy
    cB
    cB
    r2al
    @4
    vx
    vy
    cA
    cA
    r2al
    3imtr4g
    anim12d
    vx
    vy
    cB
    cR
    df-so
    vx
    vy
    cA
    cR
    df-so
    3imtr4g
end
