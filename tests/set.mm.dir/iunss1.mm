include "wss.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "ssrexv.mm"
include "eliun.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem iunss1
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
  assert |- ( A C_ B -> U_ x e. A C C_ U_ x e. B C )

  proof
    cA
    cB
    wss
    #
    vy
    vx
    cA
    cC
    ciun
    #
    vx
    cB
    cC
    ciun
    #
    @0
    vy
    cv
    #
    cC
    wcel
    #
    vx
    cA
    wrex
    @4
    vx
    cB
    wrex
    @3
    @1
    wcel
    @3
    @2
    wcel
    @4
    vx
    cA
    cB
    ssrexv
    vx
    @3
    cA
    cC
    eliun
    vx
    @3
    cB
    cC
    eliun
    3imtr4g
    ssrdv
end
