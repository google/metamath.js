include "wceq.mm"
include "wpss.mm"
include "wb.mm"
include "psseq2.mm"
include "ax-mp.mm"

theorem psseq2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume psseq1i.1: |- A = B


  assert |- ( C C. A <-> C C. B )

  proof
    cA
    cB
    wceq
    cC
    cA
    wpss
    cC
    cB
    wpss
    wb
    psseq1i.1
    cA
    cB
    cC
    psseq2
    ax-mp
end
