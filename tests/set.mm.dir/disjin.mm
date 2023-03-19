include "cv.mm"
include "wcel.mm"
include "wrmo.mm"
include "wal.mm"
include "cin.mm"
include "wdisj.mm"
include "wa.mm"
include "wi.mm"
include "elinel1.mm"
include "anim2i.mm"
include "ax-gen.mm"
include "rmoimi2.mm"
include "alimi.mm"
include "df-disj.mm"
include "3imtr4i.mm"

theorem disjin
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y


  assert |- ( Disj_ x e. B C -> Disj_ x e. B ( C i^i A ) )

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
    cC
    cA
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
    cC
    cA
    elinel1
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
