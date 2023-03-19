include "wceq.mm"
include "cqs.mm"
include "qseq1.mm"
include "ax-mp.mm"

theorem qseq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume qseq1i.1: |- A = B


  assert |- ( A /. C ) = ( B /. C )

  proof
    cA
    cB
    wceq
    cA
    cC
    cqs
    cB
    cC
    cqs
    wceq
    qseq1i.1
    cA
    cB
    cC
    qseq1
    ax-mp
end
