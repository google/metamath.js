include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "csqrt.mm"
include "cfv.mm"
include "sqrtge0.mm"
include "mpan.mm"

theorem sqrtge0i
  let cA: class A
  assume sqrth.1: |- A e. RR


  assert |- ( 0 <_ A -> 0 <_ ( sqrt ` A ) )

  proof
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cc0
    cA
    csqrt
    cfv
    cle
    wbr
    sqrth.1
    cA
    sqrtge0
    mpan
end
