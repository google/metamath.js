include "chil.mm"
include "wcel.mm"
include "csn.mm"
include "cort.mm"
include "cfv.mm"
include "cspn.mm"
include "h1did.mm"
include "spansn.mm"
include "eleqtrrd.mm"

theorem spansnid
  let cA: class A


  assert |- ( A e. ~H -> A e. ( span ` { A } ) )

  proof
    cA
    chil
    wcel
    cA
    cA
    csn
    #
    cort
    cfv
    cort
    cfv
    @0
    cspn
    cfv
    cA
    h1did
    cA
    spansn
    eleqtrrd
end
