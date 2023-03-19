include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wal.mm"
include "wdisj.mm"
include "wi.mm"
include "ssel.mm"
include "anim1d.mm"
include "alrimiv.mm"
include "moim.mm"
include "syl.mm"
include "alimdv.mm"
include "dfdisj2.mm"
include "3imtr4g.mm"

theorem disjss1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( A C_ B -> ( Disj_ x e. B C -> Disj_ x e. A C ) )

  proof
    cA
    cB
    wss
    #
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    cC
    wcel
    #
    wa
    #
    vx
    wmo
    #
    vy
    wal
    @1
    cA
    wcel
    #
    @3
    wa
    #
    vx
    wmo
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
    @5
    @8
    vy
    @0
    @7
    @4
    wi
    #
    vx
    wal
    @5
    @8
    wi
    @0
    @9
    vx
    @0
    @6
    @2
    @3
    cA
    cB
    @1
    ssel
    anim1d
    alrimiv
    @7
    @4
    vx
    moim
    syl
    alimdv
    vx
    vy
    cB
    cC
    dfdisj2
    vx
    vy
    cA
    cC
    dfdisj2
    3imtr4g
end
