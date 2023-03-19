include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"

theorem fvexi
  let cA: class A
  let cB: class B
  let cF: class F
  assume fvexi.1: |- A = ( F ` B )


  assert |- A e. _V

  proof
    cA
    cB
    cF
    cfv
    cvv
    fvexi.1
    cB
    cF
    fvex
    eqeltri
end
