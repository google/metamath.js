include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "rankon.mm"
include "onirri.mm"
include "rankelb.mm"
include "mtoi.mm"

theorem wfelirr
  let cA: class A


  assert |- ( A e. U. ( R1 " On ) -> -. A e. A )

  proof
    cA
    cr1
    con0
    cima
    cuni
    wcel
    cA
    cA
    wcel
    cA
    crnk
    cfv
    #
    @0
    wcel
    @0
    cA
    rankon
    onirri
    cA
    cA
    rankelb
    mtoi
end
