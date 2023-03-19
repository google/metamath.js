include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wrmo.mm"
include "wal.mm"
include "wdisj.mm"
include "ssrmo.mm"
include "alimdv.mm"
include "df-disj.mm"
include "3imtr4g.mm"

theorem disjss1f
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume disjss1f.1: |- F/_ x A
  assume disjss1f.2: |- F/_ x B


  assert |- ( A C_ B -> ( Disj_ x e. B C -> Disj_ x e. A C ) )

  proof
    cA
    cB
    wss
    #
    vy
    cv
    cC
    wcel
    #
    vx
    cB
    wrmo
    #
    vy
    wal
    @1
    vx
    cA
    wrmo
    #
    vy
    wal
    vx
    cB
    cC
    wdisj
    vx
    cA
    cC
    wdisj
    @0
    @2
    @3
    vy
    @1
    vx
    cA
    cB
    disjss1f.1
    disjss1f.2
    ssrmo
    alimdv
    vx
    vy
    cB
    cC
    df-disj
    vx
    vy
    cA
    cC
    df-disj
    3imtr4g
end
