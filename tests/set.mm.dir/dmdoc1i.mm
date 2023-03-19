include "cort.mm"
include "cfv.mm"
include "ccm.mm"
include "wbr.mm"
include "cdmd.mm"
include "cmidi.mm"
include "cmcm2ii.mm"
include "choccli.mm"
include "cmdmdi.mm"
include "ax-mp.mm"

theorem dmdoc1i
  let cA: class A
  assume mdoc1.1: |- A e. CH


  assert |- A MH* ( _|_ ` A )

  proof
    cA
    cA
    cort
    cfv
    #
    ccm
    wbr
    cA
    @0
    cdmd
    wbr
    cA
    cA
    mdoc1.1
    mdoc1.1
    cA
    mdoc1.1
    cmidi
    cmcm2ii
    cA
    @0
    mdoc1.1
    cA
    mdoc1.1
    choccli
    cmdmdi
    ax-mp
end
