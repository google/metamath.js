include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "csqrt.mm"
include "cfv.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "sqrtsq2.mm"
include "mpanr1.mm"
include "mpanl1.mm"
include "recni.mm"
include "sqvali.mm"
include "eqeq2i.mm"
include "syl6bb.mm"

theorem sqrtmsq2i
  let cA: class A
  let cB: class B
  assume sqrth.1: |- A e. RR
  assume sqr11.1: |- B e. RR


  assert |- ( ( 0 <_ A /\ 0 <_ B ) -> ( ( sqrt ` A ) = B <-> A = ( B x. B ) ) )

  proof
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
    wa
    cA
    csqrt
    cfv
    cB
    wceq
    #
    cA
    cB
    c2
    cexp
    co
    #
    wceq
    #
    cA
    cB
    cB
    cmul
    co
    #
    wceq
    cA
    cr
    wcel
    #
    @0
    @1
    @2
    @4
    wb
    #
    sqrth.1
    @6
    @0
    wa
    cB
    cr
    wcel
    @1
    @7
    sqr11.1
    cA
    cB
    sqrtsq2
    mpanr1
    mpanl1
    @3
    @5
    cA
    cB
    cB
    sqr11.1
    recni
    sqvali
    eqeq2i
    syl6bb
end
