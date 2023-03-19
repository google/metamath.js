include "cpr.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "elprg.mm"
include "ibi.mm"

theorem elpri
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. { B , C } -> ( A = B \/ A = C ) )

  proof
    cA
    cB
    cC
    cpr
    #
    wcel
    cA
    cB
    wceq
    cA
    cC
    wceq
    wo
    cA
    cB
    cC
    @0
    elprg
    ibi
end
