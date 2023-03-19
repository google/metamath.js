include "wss.mm"
include "wa.mm"
include "ciun.mm"
include "wceq.mm"
include "iunss1.mm"
include "anim12i.mm"
include "eqss.mm"
include "3imtr4i.mm"

theorem iuneq1
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
  assert |- ( A = B -> U_ x e. A C = U_ x e. B C )

  proof
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wa
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
    wss
    #
    @3
    @2
    wss
    #
    wa
    cA
    cB
    wceq
    @2
    @3
    wceq
    @0
    @4
    @1
    @5
    vx
    cA
    cB
    cC
    iunss1
    vx
    cB
    cA
    cC
    iunss1
    anim12i
    cA
    cB
    eqss
    @2
    @3
    eqss
    3imtr4i
end
