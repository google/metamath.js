include "wceq.mm"
include "cpr.mm"
include "preq1.mm"
include "ax-mp.mm"

theorem preq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume preq1i.1: |- A = B


  assert |- { A , C } = { B , C }

  proof
    cA
    cB
    wceq
    cA
    cC
    cpr
    cB
    cC
    cpr
    wceq
    preq1i.1
    cA
    cB
    cC
    preq1
    ax-mp
end
