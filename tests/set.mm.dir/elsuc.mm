include "cvv.mm"
include "wcel.mm"
include "csuc.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "elsucg.mm"
include "ax-mp.mm"

theorem elsuc
  let cA: class A
  let cB: class B
  assume elsuc.1: |- A e. _V


  assert |- ( A e. suc B <-> ( A e. B \/ A = B ) )

  proof
    cA
    cvv
    wcel
    cA
    cB
    csuc
    wcel
    cA
    cB
    wcel
    cA
    cB
    wceq
    wo
    wb
    elsuc.1
    cA
    cB
    cvv
    elsucg
    ax-mp
end
