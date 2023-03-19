include "cort.mm"
include "cfv.mm"
include "cmd.mm"
include "choccli.mm"
include "mdoc1i.mm"
include "ococi.mm"
include "breqtri.mm"

theorem mdoc2i
  let cA: class A
  assume mdoc1.1: |- A e. CH


  assert |- ( _|_ ` A ) MH A

  proof
    cA
    cort
    cfv
    #
    @0
    cort
    cfv
    cA
    cmd
    @0
    cA
    mdoc1.1
    choccli
    mdoc1i
    cA
    mdoc1.1
    ococi
    breqtri
end
