include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "snidg.mm"
include "elex.mm"
include "impbii.mm"

theorem snidb
  let cA: class A


  assert |- ( A e. _V <-> A e. { A } )

  proof
    cA
    cvv
    wcel
    cA
    cA
    csn
    #
    wcel
    cA
    cvv
    snidg
    cA
    @0
    elex
    impbii
end
