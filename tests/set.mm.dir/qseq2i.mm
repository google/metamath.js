include "wceq.mm"
include "cqs.mm"
include "qseq2.mm"
include "ax-mp.mm"

theorem qseq2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume qseq2i.1: |- A = B


  assert |- ( C /. A ) = ( C /. B )

  proof
    cA
    cB
    wceq
    cC
    cA
    cqs
    cC
    cB
    cqs
    wceq
    qseq2i.1
    cA
    cB
    cC
    qseq2
    ax-mp
end
