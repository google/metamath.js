include "wss.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wrmo.mm"
include "wal.mm"
include "wdisj.mm"
include "wi.mm"
include "ssel.mm"
include "ralimi.mm"
include "rmoim.mm"
include "syl.mm"
include "alimdv.mm"
include "df-disj.mm"
include "3imtr4g.mm"

theorem disjss2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y


  assert |- ( A. x e. A B C_ C -> ( Disj_ x e. A C -> Disj_ x e. A B ) )

  proof
    cB
    cC
    wss
    #
    vx
    cA
    wral
    #
    vy
    cv
    #
    cC
    wcel
    #
    vx
    cA
    wrmo
    #
    vy
    wal
    @2
    cB
    wcel
    #
    vx
    cA
    wrmo
    #
    vy
    wal
    vx
    cA
    cC
    wdisj
    vx
    cA
    cB
    wdisj
    @1
    @4
    @6
    vy
    @1
    @5
    @3
    wi
    #
    vx
    cA
    wral
    @4
    @6
    wi
    @0
    @7
    vx
    cA
    cB
    cC
    @2
    ssel
    ralimi
    @5
    @3
    vx
    cA
    rmoim
    syl
    alimdv
    vx
    vy
    cA
    cC
    df-disj
    vx
    vy
    cA
    cB
    df-disj
    3imtr4g
end
