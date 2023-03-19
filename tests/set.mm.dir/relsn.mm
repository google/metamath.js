include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "wrel.mm"
include "cxp.mm"
include "wb.mm"
include "relsng.mm"
include "ax-mp.mm"

theorem relsn
  let cA: class A
  assume relsn.1: |- A e. _V


  assert |- ( Rel { A } <-> A e. ( _V X. _V ) )

  proof
    cA
    cvv
    wcel
    cA
    csn
    wrel
    cA
    cvv
    cvv
    cxp
    wcel
    wb
    relsn.1
    cA
    cvv
    relsng
    ax-mp
end
