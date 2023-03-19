include "c0.mm"
include "cv.mm"
include "c-bnj14.mm"
include "cop.mm"
include "csn.mm"
include "cvv.mm"
include "snex.mm"
include "eqeltri.mm"

theorem bnj95
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cF: class F
  assume bnj95.1: |- F = { <. (/) , _pred ( x , A , R ) >. }


  assert |- F e. _V

  proof
    cF
    c0
    cA
    cR
    vx
    cv
    c-bnj14
    cop
    #
    csn
    cvv
    bnj95.1
    @0
    snex
    eqeltri
end
