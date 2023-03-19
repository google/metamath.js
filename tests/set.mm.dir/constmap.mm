include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "wf.mm"
include "cmap.mm"
include "co.mm"
include "fconst6g.mm"
include "elmap.mm"
include "sylibr.mm"

theorem constmap
  let cA: class A
  let cB: class B
  let cC: class C
  assume constmap.1: |- A e. _V
  assume constmap.3: |- C e. _V


  assert |- ( B e. C -> ( A X. { B } ) e. ( C ^m A ) )

  proof
    cB
    cC
    wcel
    cA
    cC
    cA
    cB
    csn
    cxp
    #
    wf
    @0
    cC
    cA
    cmap
    co
    wcel
    cA
    cB
    cC
    fconst6g
    cC
    cA
    @0
    constmap.3
    constmap.1
    elmap
    sylibr
end
