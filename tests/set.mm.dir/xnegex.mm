include "cxne.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "cneg.mm"
include "cif.mm"
include "cvv.mm"
include "df-xneg.mm"
include "cxr.mm"
include "mnfxr.mm"
include "elexi.mm"
include "pnfex.mm"
include "negex.mm"
include "ifex.mm"
include "eqeltri.mm"

theorem xnegex
  let cA: class A


  assert |- -e A e. _V

  proof
    cA
    cxne
    cA
    cpnf
    wceq
    #
    cmnf
    cA
    cmnf
    wceq
    #
    cpnf
    cA
    cneg
    #
    cif
    #
    cif
    cvv
    cA
    df-xneg
    @0
    cmnf
    @3
    cmnf
    cxr
    mnfxr
    elexi
    @1
    cpnf
    @2
    pnfex
    cA
    negex
    ifex
    ifex
    eqeltri
end
