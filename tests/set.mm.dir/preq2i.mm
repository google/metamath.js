include "wceq.mm"
include "cpr.mm"
include "preq2.mm"
include "ax-mp.mm"

theorem preq2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume preq1i.1: |- A = B


  assert |- { C , A } = { C , B }

  proof
    cA
    cB
    wceq
    cC
    cA
    cpr
    cC
    cB
    cpr
    wceq
    preq1i.1
    cA
    cB
    cC
    preq2
    ax-mp
end
