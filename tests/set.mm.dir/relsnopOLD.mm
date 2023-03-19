include "cop.mm"
include "csn.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "opelvv.mm"
include "opex.mm"
include "relsn.mm"
include "mpbir.mm"

theorem relsnopOLD
  let cA: class A
  let cB: class B
  assume relsn.1: |- A e. _V
  assume relsnop.2: |- B e. _V


  assert |- Rel { <. A , B >. }

  proof
    cA
    cB
    cop
    #
    csn
    wrel
    @0
    cvv
    cvv
    cxp
    wcel
    cA
    cB
    relsn.1
    relsnop.2
    opelvv
    @0
    cA
    cB
    opex
    relsn
    mpbir
end
