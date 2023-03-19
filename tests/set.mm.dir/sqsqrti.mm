include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "csqrt.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "resqrtth.mm"
include "mpan.mm"

theorem sqsqrti
  let cA: class A
  assume sqrth.1: |- A e. RR


  assert |- ( 0 <_ A -> ( ( sqrt ` A ) ^ 2 ) = A )

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
    c2
    cexp
    co
    cA
    wceq
    sqrth.1
    cA
    resqrtth
    mpan
end
