include "wceq.mm"
include "wfn.mm"
include "wb.mm"
include "fneq2.mm"
include "ax-mp.mm"

theorem fneq2i
  let cA: class A
  let cB: class B
  let cF: class F
  assume fneq2i.1: |- A = B


  assert |- ( F Fn A <-> F Fn B )

  proof
    cA
    cB
    wceq
    cF
    cA
    wfn
    cF
    cB
    wfn
    wb
    fneq2i.1
    cA
    cB
    cF
    fneq2
    ax-mp
end
