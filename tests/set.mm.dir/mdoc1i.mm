include "cort.mm"
include "cfv.mm"
include "ccm.mm"
include "wbr.mm"
include "cmd.mm"
include "cmidi.mm"
include "cmcm2ii.mm"
include "choccli.mm"
include "cmmdi.mm"
include "ax-mp.mm"

theorem mdoc1i
  let cA: class A
  assume mdoc1.1: |- A e. CH


  assert |- A MH ( _|_ ` A )

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
    cmd
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
    cmmdi
    ax-mp
end
