include "cr.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "cc.mm"
include "wb.mm"
include "recn.mm"
include "rereb.mm"
include "syl.mm"
include "ibi.mm"

theorem rere
  let cA: class A


  assert |- ( A e. RR -> ( Re ` A ) = A )

  proof
    cA
    cr
    wcel
    #
    cA
    cre
    cfv
    cA
    wceq
    #
    @0
    cA
    cc
    wcel
    @0
    @1
    wb
    cA
    recn
    cA
    rereb
    syl
    ibi
end
