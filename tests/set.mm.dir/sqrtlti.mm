include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "csqrt.mm"
include "cfv.mm"
include "wb.mm"
include "wa.mm"
include "sqrtlt.mm"
include "mpanr1.mm"
include "mpanl1.mm"

theorem sqrtlti
  let cA: class A
  let cB: class B
  assume sqrth.1: |- A e. RR
  assume sqr11.1: |- B e. RR


  assert |- ( ( 0 <_ A /\ 0 <_ B ) -> ( A < B <-> ( sqrt ` A ) < ( sqrt ` B ) ) )

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
    clt
    wbr
    cA
    csqrt
    cfv
    cB
    csqrt
    cfv
    clt
    wbr
    wb
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
    sqrtlt
    mpanr1
    mpanl1
end
