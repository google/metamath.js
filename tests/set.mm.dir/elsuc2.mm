include "cvv.mm"
include "wcel.mm"
include "csuc.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "elsuc2g.mm"
include "ax-mp.mm"

theorem elsuc2
  let cA: class A
  let cB: class B
  assume elsuc.1: |- A e. _V


  assert |- ( B e. suc A <-> ( B e. A \/ B = A ) )

  proof
    cA
    cvv
    wcel
    cB
    cA
    csuc
    wcel
    cB
    cA
    wcel
    cB
    cA
    wceq
    wo
    wb
    elsuc.1
    cB
    cA
    cvv
    elsuc2g
    ax-mp
end
