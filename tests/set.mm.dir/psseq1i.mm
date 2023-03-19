include "wceq.mm"
include "wpss.mm"
include "wb.mm"
include "psseq1.mm"
include "ax-mp.mm"

theorem psseq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume psseq1i.1: |- A = B


  assert |- ( A C. C <-> B C. C )

  proof
    cA
    cB
    wceq
    cA
    cC
    wpss
    cB
    cC
    wpss
    wb
    psseq1i.1
    cA
    cB
    cC
    psseq1
    ax-mp
end
