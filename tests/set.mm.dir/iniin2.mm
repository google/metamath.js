include "c0.mm"
include "wne.mm"
include "cin.mm"
include "ciin.mm"
include "iinin2.mm"
include "eqcomd.mm"

theorem iniin2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  assert |- ( A =/= (/) -> ( B i^i |^|_ x e. A C ) = |^|_ x e. A ( B i^i C ) )

  proof
    cA
    c0
    wne
    vx
    cA
    cB
    cC
    cin
    ciin
    cB
    vx
    cA
    cC
    ciin
    cin
    vx
    cA
    cB
    cC
    iinin2
    eqcomd
end
