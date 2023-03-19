include "wceq.mm"
include "cfv.mm"
include "fveq1.mm"
include "ax-mp.mm"

theorem fveq1i
  let cA: class A
  let cF: class F
  let cG: class G
  assume fveq1i.1: |- F = G


  assert |- ( F ` A ) = ( G ` A )

  proof
    cF
    cG
    wceq
    cA
    cF
    cfv
    cA
    cG
    cfv
    wceq
    fveq1i.1
    cA
    cF
    cG
    fveq1
    ax-mp
end
