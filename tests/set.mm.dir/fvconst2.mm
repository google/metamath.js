include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "cfv.mm"
include "wceq.mm"
include "fvconst2g.mm"
include "mpan.mm"

theorem fvconst2
  let cA: class A
  let cB: class B
  let cC: class C
  assume fvconst2.1: |- B e. _V


  assert |- ( C e. A -> ( ( A X. { B } ) ` C ) = B )

  proof
    cB
    cvv
    wcel
    cC
    cA
    wcel
    cC
    cA
    cB
    csn
    cxp
    cfv
    cB
    wceq
    fvconst2.1
    cA
    cB
    cC
    cvv
    fvconst2g
    mpan
end
