include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "crnk.mm"
include "cdm.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "rankf.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"

theorem rankvaln
  let cA: class A


  assert |- ( -. A e. U. ( R1 " On ) -> ( rank ` A ) = (/) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    cA
    crnk
    cdm
    #
    wcel
    cA
    crnk
    cfv
    c0
    wceq
    @1
    @0
    cA
    @0
    con0
    crnk
    rankf
    fdmi
    eleq2i
    cA
    crnk
    ndmfv
    sylnbir
end
