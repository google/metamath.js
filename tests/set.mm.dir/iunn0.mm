include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wrex.mm"
include "ciun.mm"
include "c0.mm"
include "wne.mm"
include "rexcom4.mm"
include "eliun.mm"
include "exbii.mm"
include "bitr4i.mm"
include "n0.mm"
include "rexbii.mm"
include "3bitr4i.mm"

theorem iunn0
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( E. x e. A B =/= (/) <-> U_ x e. A B =/= (/) )

  proof
    vy
    cv
    #
    cB
    wcel
    #
    vy
    wex
    #
    vx
    cA
    wrex
    #
    @0
    vx
    cA
    cB
    ciun
    #
    wcel
    #
    vy
    wex
    #
    cB
    c0
    wne
    #
    vx
    cA
    wrex
    @4
    c0
    wne
    @3
    @1
    vx
    cA
    wrex
    #
    vy
    wex
    @6
    @1
    vx
    vy
    cA
    rexcom4
    @5
    @8
    vy
    vx
    @0
    cA
    cB
    eliun
    exbii
    bitr4i
    @7
    @2
    vx
    cA
    vy
    cB
    n0
    rexbii
    vy
    @4
    n0
    3bitr4i
end
