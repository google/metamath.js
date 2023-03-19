include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "breq2.mm"
include "ax-mp.mm"

theorem breq2i
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume breq1i.1: |- A = B


  assert |- ( C R A <-> C R B )

  proof
    cA
    cB
    wceq
    cC
    cA
    cR
    wbr
    cC
    cB
    cR
    wbr
    wb
    breq1i.1
    cA
    cB
    cC
    cR
    breq2
    ax-mp
end
