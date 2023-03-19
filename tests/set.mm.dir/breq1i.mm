include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "breq1.mm"
include "ax-mp.mm"

theorem breq1i
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume breq1i.1: |- A = B


  assert |- ( A R C <-> B R C )

  proof
    cA
    cB
    wceq
    cA
    cC
    cR
    wbr
    cB
    cC
    cR
    wbr
    wb
    breq1i.1
    cA
    cB
    cC
    cR
    breq1
    ax-mp
end
