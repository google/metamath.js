include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "wceq.mm"
include "sqrtmuli.mm"
include "mp2an.mm"

theorem sqrtmulii
  let cA: class A
  let cB: class B
  assume sqrth.1: |- A e. RR
  assume sqr11.1: |- B e. RR
  assume sqrmuli.1: |- 0 <_ A
  assume sqrmuli.2: |- 0 <_ B


  assert |- ( sqrt ` ( A x. B ) ) = ( ( sqrt ` A ) x. ( sqrt ` B ) )

  proof
    cc0
    cA
    cle
    wbr
    cc0
    cB
    cle
    wbr
    cA
    cB
    cmul
    co
    csqrt
    cfv
    cA
    csqrt
    cfv
    cB
    csqrt
    cfv
    cmul
    co
    wceq
    sqrmuli.1
    sqrmuli.2
    cA
    cB
    sqrth.1
    sqr11.1
    sqrtmuli
    mp2an
end
