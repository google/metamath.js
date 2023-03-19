include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "wceq.mm"
include "sqrtmsq.mm"
include "mpan.mm"

theorem sqrtmsqi
  let cA: class A
  assume sqrth.1: |- A e. RR


  assert |- ( 0 <_ A -> ( sqrt ` ( A x. A ) ) = A )

  proof
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cA
    cA
    cmul
    co
    csqrt
    cfv
    cA
    wceq
    sqrth.1
    cA
    sqrtmsq
    mpan
end
