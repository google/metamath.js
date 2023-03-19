include "wlim.mm"
include "cuni.mm"
include "wceq.mm"
include "wb.mm"
include "limuni.mm"
include "limeq.mm"
include "syl.mm"
include "ibi.mm"

theorem limuni2
  let cA: class A


  assert |- ( Lim A -> Lim U. A )

  proof
    cA
    wlim
    #
    cA
    cuni
    #
    wlim
    #
    @0
    cA
    @1
    wceq
    @0
    @2
    wb
    cA
    limuni
    cA
    @1
    limeq
    syl
    ibi
end
