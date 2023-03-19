include "wceq.mm"
include "cfv.mm"
include "fveq2.mm"
include "ax-mp.mm"

theorem fveq2i
  let cA: class A
  let cB: class B
  let cF: class F
  assume fveq2i.1: |- A = B


  assert |- ( F ` A ) = ( F ` B )

  proof
    cA
    cB
    wceq
    cA
    cF
    cfv
    cB
    cF
    cfv
    wceq
    fveq2i.1
    cA
    cB
    cF
    fveq2
    ax-mp
end
