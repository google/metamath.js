include "wss.mm"
include "wrex.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "ssel.mm"
include "reximi.mm"
include "r19.37v.mm"
include "syl.mm"
include "eliun.mm"
include "syl6ibr.mm"
include "ssrdv.mm"

theorem ssiun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint C x
  disjoint x y
  disjoint C y
  disjoint A y
  disjoint B y
  assert |- ( E. x e. A C C_ B -> C C_ U_ x e. A B )

  proof
    cC
    cB
    wss
    #
    vx
    cA
    wrex
    #
    vy
    cC
    vx
    cA
    cB
    ciun
    #
    @1
    vy
    cv
    #
    cC
    wcel
    #
    @3
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    @3
    @2
    wcel
    @1
    @4
    @5
    wi
    #
    vx
    cA
    wrex
    @4
    @6
    wi
    @0
    @7
    vx
    cA
    cC
    cB
    @3
    ssel
    reximi
    @4
    @5
    vx
    cA
    r19.37v
    syl
    vx
    @3
    cA
    cB
    eliun
    syl6ibr
    ssrdv
end
