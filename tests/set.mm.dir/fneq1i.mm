include "wceq.mm"
include "wfn.mm"
include "wb.mm"
include "fneq1.mm"
include "ax-mp.mm"

theorem fneq1i
  let cA: class A
  let cF: class F
  let cG: class G
  assume fneq1i.1: |- F = G


  assert |- ( F Fn A <-> G Fn A )

  proof
    cF
    cG
    wceq
    cF
    cA
    wfn
    cG
    cA
    wfn
    wb
    fneq1i.1
    cA
    cF
    cG
    fneq1
    ax-mp
end
