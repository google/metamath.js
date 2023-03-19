include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "wa.mm"
include "n0i.mm"
include "cxp.mm"
include "wfn.mm"
include "cdm.mm"
include "fnmap.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "nsyl2.mm"

theorem elmapex
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B ^m C ) -> ( B e. _V /\ C e. _V ) )

  proof
    cA
    cB
    cC
    cmap
    co
    #
    wcel
    @0
    c0
    wceq
    cB
    cvv
    wcel
    cC
    cvv
    wcel
    wa
    @0
    cA
    n0i
    cB
    cC
    cvv
    cmap
    cmap
    cvv
    cvv
    cxp
    #
    wfn
    cmap
    cdm
    @1
    wceq
    fnmap
    @1
    cmap
    fndm
    ax-mp
    ndmov
    nsyl2
end
