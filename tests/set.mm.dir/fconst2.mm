include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "wf.mm"
include "cxp.mm"
include "wceq.mm"
include "wb.mm"
include "fconst2g.mm"
include "ax-mp.mm"

theorem fconst2
  let cA: class A
  let cB: class B
  let cF: class F
  assume fvconst2.1: |- B e. _V


  assert |- ( F : A --> { B } <-> F = ( A X. { B } ) )

  proof
    cB
    cvv
    wcel
    cA
    cB
    csn
    #
    cF
    wf
    cF
    cA
    @0
    cxp
    wceq
    wb
    fvconst2.1
    cA
    cB
    cvv
    cF
    fconst2g
    ax-mp
end
