include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "elin.mm"
include "bitri.mm"
include "eqriv.mm"

theorem ineqri
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume ineqri.1: |- ( ( x e. A /\ x e. B ) <-> x e. C )

  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( A i^i B ) = C

  proof
    vx
    cA
    cB
    cin
    #
    cC
    vx
    cv
    #
    @0
    wcel
    @1
    cA
    wcel
    @1
    cB
    wcel
    wa
    @1
    cC
    wcel
    @1
    cA
    cB
    elin
    ineqri.1
    bitri
    eqriv
end
