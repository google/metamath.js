include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "ciun.mm"
include "ssiun.mm"
include "ralimi.mm"
include "iunss.mm"
include "sylibr.mm"

theorem iunss2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D

  disjoint x y
  disjoint B x
  disjoint C y
  disjoint D x
  assert |- ( A. x e. A E. y e. B C C_ D -> U_ x e. A C C_ U_ y e. B D )

  proof
    cC
    cD
    wss
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    cC
    vy
    cB
    cD
    ciun
    #
    wss
    #
    vx
    cA
    wral
    vx
    cA
    cC
    ciun
    @1
    wss
    @0
    @2
    vx
    cA
    vy
    cB
    cD
    cC
    ssiun
    ralimi
    vx
    cA
    cC
    @1
    iunss
    sylibr
end
