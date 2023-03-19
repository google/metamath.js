include "ctp.mm"
include "wcel.mm"
include "wceq.mm"
include "w3o.mm"
include "eltpg.mm"
include "ibi.mm"

theorem eltpi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A e. { B , C , D } -> ( A = B \/ A = C \/ A = D ) )

  proof
    cA
    cB
    cC
    cD
    ctp
    #
    wcel
    cA
    cB
    wceq
    cA
    cC
    wceq
    cA
    cD
    wceq
    w3o
    cA
    cB
    cC
    cD
    @0
    eltpg
    ibi
end
