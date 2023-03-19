include "wceq.mm"
include "cmpt.mm"
include "mpteq1.mm"
include "ax-mp.mm"

theorem mpteq1i
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume mpteq1i.1: |- A = B

  disjoint A x
  disjoint B x
  assert |- ( x e. A |-> C ) = ( x e. B |-> C )

  proof
    cA
    cB
    wceq
    vx
    cA
    cC
    cmpt
    vx
    cB
    cC
    cmpt
    wceq
    mpteq1i.1
    vx
    cA
    cB
    cC
    mpteq1
    ax-mp
end
