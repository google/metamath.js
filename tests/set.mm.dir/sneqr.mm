include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "wi.mm"
include "sneqrg.mm"
include "ax-mp.mm"

theorem sneqr
  let cA: class A
  let cB: class B
  assume sneqr.1: |- A e. _V


  assert |- ( { A } = { B } -> A = B )

  proof
    cA
    cvv
    wcel
    cA
    csn
    cB
    csn
    wceq
    cA
    cB
    wceq
    wi
    sneqr.1
    cA
    cB
    cvv
    sneqrg
    ax-mp
end
