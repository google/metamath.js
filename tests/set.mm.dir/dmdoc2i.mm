include "cort.mm"
include "cfv.mm"
include "cdmd.mm"
include "choccli.mm"
include "dmdoc1i.mm"
include "ococi.mm"
include "breqtri.mm"

theorem dmdoc2i
  let cA: class A
  assume mdoc1.1: |- A e. CH


  assert |- ( _|_ ` A ) MH* A

  proof
    cA
    cort
    cfv
    #
    @0
    cort
    cfv
    cA
    cdmd
    @0
    cA
    mdoc1.1
    choccli
    dmdoc1i
    cA
    mdoc1.1
    ococi
    breqtri
end
