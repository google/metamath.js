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
include "wa.mm"
include "sqrtmul.mm"
include "mpanr1.mm"
include "mpanl1.mm"

theorem sqrtmuli
  let cA: class A
  let cB: class B
  assume sqrth.1: |- A e. RR
  assume sqr11.1: |- B e. RR


  assert |- ( ( 0 <_ A /\ 0 <_ B ) -> ( sqrt ` ( A x. B ) ) = ( ( sqrt ` A ) x. ( sqrt ` B ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cc0
    cB
    cle
    wbr
    #
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
    #
    sqrth.1
    @0
    @1
    wa
    cB
    cr
    wcel
    @2
    @3
    sqr11.1
    cA
    cB
    sqrtmul
    mpanr1
    mpanl1
end
