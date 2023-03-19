include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "csqrt.mm"
include "cfv.mm"
include "sqrtgt0.mm"
include "mpan.mm"

theorem sqrtgt0i
  let cA: class A
  assume sqrth.1: |- A e. RR


  assert |- ( 0 < A -> 0 < ( sqrt ` A ) )

  proof
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    cc0
    cA
    csqrt
    cfv
    clt
    wbr
    sqrth.1
    cA
    sqrtgt0
    mpan
end
