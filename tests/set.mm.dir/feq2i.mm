include "wceq.mm"
include "wf.mm"
include "wb.mm"
include "feq2.mm"
include "ax-mp.mm"

theorem feq2i
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume feq2i.1: |- A = B


  assert |- ( F : A --> C <-> F : B --> C )

  proof
    cA
    cB
    wceq
    cA
    cC
    cF
    wf
    cB
    cC
    cF
    wf
    wb
    feq2i.1
    cA
    cB
    cC
    cF
    feq2
    ax-mp
end
