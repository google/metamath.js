include "cvv.mm"
include "wcel.mm"
include "cuni.mm"
include "uniexg.mm"
include "uniexr.mm"
include "impbii.mm"

theorem uniexb
  let cA: class A


  assert |- ( A e. _V <-> U. A e. _V )

  proof
    cA
    cvv
    wcel
    cA
    cuni
    cvv
    wcel
    cA
    cvv
    uniexg
    cA
    cvv
    uniexr
    impbii
end
