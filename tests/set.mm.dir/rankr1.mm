include "cvv.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "wceq.mm"
include "cr1.mm"
include "wn.mm"
include "csuc.mm"
include "wa.mm"
include "wb.mm"
include "rankr1g.mm"
include "ax-mp.mm"

theorem rankr1
  let cA: class A
  let cB: class B
  assume rankid.1: |- A e. _V


  assert |- ( B = ( rank ` A ) <-> ( -. A e. ( R1 ` B ) /\ A e. ( R1 ` suc B ) ) )

  proof
    cA
    cvv
    wcel
    cB
    cA
    crnk
    cfv
    wceq
    cA
    cB
    cr1
    cfv
    wcel
    wn
    cA
    cB
    csuc
    cr1
    cfv
    wcel
    wa
    wb
    rankid.1
    cA
    cB
    cvv
    rankr1g
    ax-mp
end
