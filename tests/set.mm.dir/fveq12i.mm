include "cfv.mm"
include "fveq1i.mm"
include "fveq2i.mm"
include "eqtri.mm"

theorem fveq12i
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  assume fveq12i.1: |- F = G
  assume fveq12i.2: |- A = B


  assert |- ( F ` A ) = ( G ` B )

  proof
    cA
    cF
    cfv
    cA
    cG
    cfv
    cB
    cG
    cfv
    cA
    cF
    cG
    fveq12i.1
    fveq1i
    cA
    cB
    cG
    fveq12i.2
    fveq2i
    eqtri
end
