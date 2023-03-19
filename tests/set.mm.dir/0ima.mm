include "c0.mm"
include "cima.mm"
include "crn.mm"
include "imassrn.mm"
include "rn0.mm"
include "sseqtri.mm"
include "0ss.mm"
include "eqssi.mm"

theorem 0ima
  let cA: class A


  assert |- ( (/) " A ) = (/)

  proof
    c0
    cA
    cima
    #
    c0
    @0
    c0
    crn
    c0
    c0
    cA
    imassrn
    rn0
    sseqtri
    @0
    0ss
    eqssi
end
