include "cv.mm"
include "wcel.mm"
include "wrmo.mm"
include "wal.mm"
include "cin.mm"
include "wdisj.mm"
include "wa.mm"
include "wi.mm"
include "elinel2.mm"
include "anim2i.mm"
include "ax-gen.mm"
include "rmoimi2.mm"
include "alimi.mm"
include "df-disj.mm"
include "3imtr4i.mm"

theorem disjin2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y


  assert |- ( Disj_ x e. B C -> Disj_ x e. B ( A i^i C ) )

  proof
    vy
    cv
    #
    cC
    wcel
    #
    vx
    cB
    wrmo
    #
    vy
    wal
    @0
    cA
    cC
    cin
    #
    wcel
    #
    vx
    cB
    wrmo
    #
    vy
    wal
    vx
    cB
    cC
    wdisj
    vx
    cB
    @3
    wdisj
    @2
    @5
    vy
    @4
    @1
    vx
    cB
    cB
    vx
    cv
    cB
    wcel
    #
    @4
    wa
    @6
    @1
    wa
    wi
    vx
    @4
    @1
    @6
    @0
    cA
    cC
    elinel2
    anim2i
    ax-gen
    rmoimi2
    alimi
    vx
    vy
    cB
    cC
    df-disj
    vx
    vy
    cB
    @3
    df-disj
    3imtr4i
end
