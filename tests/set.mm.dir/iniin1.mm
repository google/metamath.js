include "c0.mm"
include "wne.mm"
include "cin.mm"
include "ciin.mm"
include "iinin1.mm"
include "eqcomd.mm"

theorem iniin1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  assert |- ( A =/= (/) -> ( |^|_ x e. A C i^i B ) = |^|_ x e. A ( C i^i B ) )

  proof
    cA
    c0
    wne
    vx
    cA
    cC
    cB
    cin
    ciin
    vx
    cA
    cC
    ciin
    cB
    cin
    vx
    cA
    cB
    cC
    iinin1
    eqcomd
end
