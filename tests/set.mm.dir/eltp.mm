include "cvv.mm"
include "wcel.mm"
include "ctp.mm"
include "wceq.mm"
include "w3o.mm"
include "wb.mm"
include "eltpg.mm"
include "ax-mp.mm"

theorem eltp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume eltp.1: |- A e. _V


  assert |- ( A e. { B , C , D } <-> ( A = B \/ A = C \/ A = D ) )

  proof
    cA
    cvv
    wcel
    cA
    cB
    cC
    cD
    ctp
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
    wb
    eltp.1
    cA
    cB
    cC
    cD
    cvv
    eltpg
    ax-mp
end
