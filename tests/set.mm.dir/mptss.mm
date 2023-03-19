include "wss.mm"
include "cmpt.mm"
include "cres.mm"
include "resmpt.mm"
include "resss.mm"
include "syl6eqssr.mm"

theorem mptss
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  assert |- ( A C_ B -> ( x e. A |-> C ) C_ ( x e. B |-> C ) )

  proof
    cA
    cB
    wss
    vx
    cA
    cC
    cmpt
    vx
    cB
    cC
    cmpt
    #
    cA
    cres
    @0
    vx
    cB
    cA
    cC
    resmpt
    @0
    cA
    resss
    syl6eqssr
end
