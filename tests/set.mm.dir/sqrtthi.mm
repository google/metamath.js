include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "remsqsqrt.mm"
include "mpan.mm"

theorem sqrtthi
  let cA: class A
  assume sqrth.1: |- A e. RR


  assert |- ( 0 <_ A -> ( ( sqrt ` A ) x. ( sqrt ` A ) ) = A )

  proof
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cA
    csqrt
    cfv
    #
    @0
    cmul
    co
    cA
    wceq
    sqrth.1
    cA
    remsqsqrt
    mpan
end
