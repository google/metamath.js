include "cvv.mm"
include "wceq.mm"
include "wcel.mm"
include "nvel.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "mtbii.mm"

theorem nvelim
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( A = _V -> -. A e. B )

  proof
    cA
    cvv
    wceq
    cvv
    cB
    wcel
    #
    cA
    cB
    wcel
    #
    cB
    nvel
    @0
    @1
    wb
    cvv
    cA
    cvv
    cA
    cB
    eleq1
    eqcoms
    mtbii
end
