include "wceq.mm"
include "wf.mm"
include "wb.mm"
include "feq1.mm"
include "ax-mp.mm"

theorem feq1i
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  assume feq1i.1: |- F = G


  assert |- ( F : A --> B <-> G : A --> B )

  proof
    cF
    cG
    wceq
    cA
    cB
    cF
    wf
    cA
    cB
    cG
    wf
    wb
    feq1i.1
    cA
    cB
    cF
    cG
    feq1
    ax-mp
end
